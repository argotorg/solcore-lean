import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyMeaning

/-! The production contextual dispatcher preserves an ordinary proxy occurrence
unchanged. Empty requirements/coercions and the absence of a specialized local
initializer exclude its actual overrides; both root and full parent contexts
then yield the same authenticated proxy leaf certificate. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference

private theorem source_view
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {inner : TypeSystem.Ty}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_bypass (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

/-- Real contextual lowering supplies every proxy metadata and layout receipt.
The typed source's raw inner type is retained even when its runtime identity
normalizes staging annotations. No whole-program or source-history claim is made. -/
theorem certificate_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (notInitializer : locals.bindings.find?
      (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Certificate values source scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine certificate_of_functions found form ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [source_view program context.plan locals context.owner (some prepared) found form]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_bypass program _ prepared.caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [source_view program context.plan locals context.owner (some prepared) found form]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := CompatibleEncoding.bind_ok accepted
      refine certificate_of_functions found form ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [source_view program context.plan locals context.owner none found form]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_bypass program _ caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [source_view program context.plan locals context.owner none found form]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
