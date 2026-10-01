import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
import Solcore.Frontend.SourceCoreGeneralFunctions

/-! The real contextual traversal supplies the atomic literal certificate.
Catalog exclusion and exact empty coercions identify the ordinary emission
path, including the dedicated native numeric-evidence branch. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
open Core Frontend SourceInference

/-- Original numeric requirement IDs are retained; ordinary leaves have none. -/
def owned (form : ExpressionForm) : List RequirementId := match form with
  | .integerLiteral _ resolution => [resolution.requirement]
  | _ => []

private theorem contextualSource_atomic
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) (atomic : Atomic node.form) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  generalize form : node.form = shape at atomic
  cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_atomic (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (atomic : Atomic node.form)
    (requirements : node.requirements = owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (owned node.form).length < 0 then none else
      if owned node.form = (owned node.form).take ((owned node.form).length - 0) ++ [] then
        some ((owned node.form).take ((owned node.form).length - 0)) else none) = _
    simp
  generalize form : node.form = shape at atomic
  cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
    owned, bind, Except.bind, pure, Except.pure]

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This theorem extracts a semantic certificate from the actual contextual
compiler result. It excludes generalized initializer overrides and output
coercions by their source metadata, without any child-evaluation premise. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (atomic : Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (requirements : node.requirements = owned node.form) (coercions : node.coercions = [])
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Certificate context.solvedRequirements source id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine of_functions (values := values) found atomic unitType ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [contextualSource_atomic program context.plan locals context.owner (some prepared) found atomic]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_atomic program _ prepared.caller context child budget scope reasonAt _ found atomic requirements coercions]
        generalize form : node.form = shape at atomic
        cases atomic <;> simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_atomic program context.plan locals context.owner (some prepared) found atomic]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := bind_accepted accepted
      refine of_functions (values := values) found atomic unitType ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [contextualSource_atomic program context.plan locals context.owner none found atomic]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_atomic program _ caller context child budget scope reasonAt _ found atomic requirements coercions]
        generalize form : node.form = shape at atomic
        cases atomic <;> simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_atomic program context.plan locals context.owner none found atomic]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
