import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.Frontend.SourceCoreGeneralFunctions

/-! Ordinary local reads through the actual shared contextual traversal.
Static catalog exclusion identifies this branch; it does not assume any child
execution or derive source metadata from native projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference

private theorem contextualSource_ordinary
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp only [SourceCoreGeneralFunctions.contextualSource, found, bind, Except.bind, pure, Except.pure,
    form, ordinary, Bool.false_eq_true, ↓reduceIte]

private theorem evidence_ordinary (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

private theorem functions_read_receipts
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (lowerPolicy : policy.lowerRead source scope id (reasonAt id) =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type) ∧
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, form,
        readPolicy, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
          childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals
        try rw [bypass] at accepted
      all_goals
        cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
        | error error => simp [read] at accepted
        | ok pair =>
          obtain ⟨other, type⟩ := pair
          have metadata := metadata_of_read read
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst other
          simp only [read, form, lowerPolicy] at accepted
          cases generated : SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) with
          | error error => simp [generated] at accepted
          | ok code =>
            simp only [generated, Except.ok.injEq] at accepted
            subst lowered
            exact ⟨rfl, rfl⟩
    · simp [owner, bind, Except.bind] at accepted

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual contextual traversal supplies both low-level read receipts.
An ordinary occurrence is outside the generalized binder/initializer catalogs;
its retained requirement and coercion spines are empty. These are static
metadata conditions, with no source or Core child execution premise. -/
theorem contextual_read_receipts
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = context.owner ∧ binding.binder.id = binder)) = false)
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type) ∧
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine functions_read_receipts (values := values) (readFuel := readFuel) found form ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [contextualSource_ordinary program context.plan locals context.owner (some prepared) found form ordinary]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_ordinary program _ prepared.caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form, ordinary, Bool.false_eq_true, ↓reduceIte]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_ordinary program context.plan locals context.owner (some prepared) found form ordinary]
        simp only [bind, Except.bind, readPolicy]
      · exact congrFun (congrFun (congrFun (congrFun lowerPolicy source) scope) id) (reasonAt id)
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := bind_accepted accepted
      refine functions_read_receipts (values := values) (readFuel := readFuel) found form ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [contextualSource_ordinary program context.plan locals context.owner none found form ordinary]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_ordinary program _ caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form, ordinary, Bool.false_eq_true, ↓reduceIte]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_ordinary program context.plan locals context.owner none found form ordinary]
        simp only [bind, Except.bind, readPolicy]
      · exact congrFun (congrFun (congrFun (congrFun lowerPolicy source) scope) id) (reasonAt id)

/-- Real contextual compiler success supplies the certificate consumed by the
universal read preservation/reflection theorems. Source typing and lexical scope
alignment remain explicit; no child semantic induction hypothesis is needed. -/
theorem loweredRead_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = context.owner ∧ binding.binder.id = binder)) = false)
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered)
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) :
    LoweredRead readFuel values source sourceContext reasonAt scope id lowered := by
  obtain ⟨read, generated⟩ := contextual_read_receipts found form requirements coercions ordinary notInitializer
    readPolicy lowerPolicy accepted
  exact loweredRead_of_accepted generated read unique declarations typed

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
