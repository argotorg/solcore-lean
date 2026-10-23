import Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
import Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution
import Lean

/-! The actual authenticator identifies the same original caller and read
before its contextual substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
open Frontend SourceInference TypeSystem SourceCoreLocalEvidence
open CallableBodyMetadataViews

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

open Lean Meta Elab Tactic in
private def unfoldCheck (hypothesis : Name) : TacticM Unit := withMainContext do
  let declaration ← getLocalDeclFromUserName hypothesis
  let type ← instantiateMVars (← inferType declaration.toExpr)
  let some (_, left, _) := type.eq? | throwError "expected equation: {type}"
  let .const name _ := left.getAppFn | throwError "expected actual definition: {left}"
  let goal ← getMainGoal
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

private theorem exact_caller {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {caller : SourceSpecialization.SpecializedFunction}
    (accepted : exactCaller plan binding = .ok caller) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source := by
  unfold exactCaller at accepted
  obtain ⟨original, selected, accepted⟩ := bind_ok accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i sourceEq
  split at accepted <;> try contradiction
  cases accepted
  have selected : SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller := by
    cases actual : SourceCompilationPlan.exactSpecialization plan binding.caller with
    | error error => simp only [actual, Except.mapError, reduceCtorEq] at selected
    | ok result => simpa only [actual, Except.mapError, Except.ok.injEq] using selected
  exact ⟨selected, by simpa using sourceEq⟩

/-- Authentication checks a declaration with the complete binding metadata,
including its initializer, in the original source. -/
theorem binding_retained
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, callerAccepted, _⟩ := bind_ok accepted
  unfold exactCaller at callerAccepted
  obtain ⟨original, _selected, callerAccepted⟩ := bind_ok callerAccepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at callerAccepted
  split at callerAccepted <;> try contradiction
  split at callerAccepted <;> try contradiction
  rename_i retained
  obtain ⟨node, present, matched⟩ := List.any_eq_true.mp retained
  cases node with
  | expression expression => cases matched
  | statement statement =>
    cases statement with
    | mk sid span type form =>
      cases form <;> try cases matched
      next binder initializer =>
        cases initializer with
        | none => cases matched
        | some initializer =>
          have identities : binder = binding.binder ∧ initializer = binding.initializer :=
            of_decide_eq_true matched
          rcases identities with ⟨rfl, rfl⟩
          exact ⟨_, present, rfl⟩

/-- The original read and its caller are recovered from the real factory;
only its types and metadata are substituted in the contextual reference. -/
theorem original_lookup
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ caller original name,
      SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source ∧
      binding.source.lookupExpression? id = some original ∧
      reference.original = original.applySubstitution ((parent.map (·.substitution)).getD []) ∧
      original.form = .reference name (.local binding.binder.id) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, callerAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨⟨active, inherited⟩, contextAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨validated, _validated, accepted⟩ := bind_ok accepted
  cases validated
  have callerFacts := exact_caller callerAccepted
  have activeEq : active = ((parent.map (·.substitution)).getD []) := by
    run_tac unfoldCheck `contextAccepted
    cases parent with
    | none => cases contextAccepted; rfl
    | some parent =>
      simp only at contextAccepted
      split at contextAccepted <;> try contradiction
      cases contextAccepted
      rfl
  dsimp only at accepted
  split at accepted
  · next node found =>
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · next name localId form =>
        split at accepted
        · cases accepted
        · next same =>
          split at accepted
          · next owned ownedEq =>
            obtain ⟨available, _available, accepted⟩ := bind_ok accepted
            obtain ⟨⟨child, witnesses⟩, _factory, accepted⟩ := bind_ok accepted
            obtain ⟨validated, _witnesses, accepted⟩ := bind_ok accepted
            cases validated
            cases accepted
            change (caller.function.typedBody.applySubstitution active).lookupExpression? id = some node at found
            rw [callerFacts.2, lookupExpression_apply] at found
            cases before : binding.source.lookupExpression? id with
            | none => simp only [before, Option.map_none, reduceCtorEq] at found
            | some original =>
              have nodeEq : original.applySubstitution active = node := by
                simpa only [before, Option.map_some, Option.some.injEq] using found
              have localEq : localId = binding.binder.id := by simpa using same
              refine ⟨caller, original, name, callerFacts.1, callerFacts.2, rfl, ?_, ?_⟩
              · exact nodeEq.symm.trans (congrArg (original.applySubstitution) activeEq)
              · rw [← nodeEq, localEq] at form
                cases original with
                | mk id span type actual requirements coercions localStart =>
                  cases actual <;>
                    simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
                      reduceCtorEq] at form
                  next originalName resolution =>
                    cases resolution <;> simp only [ReferenceResolution.applySubstitution] at form <;>
                      cases form <;> rfl
          · cases accepted
      · cases accepted
  · cases accepted

/-- A prepared view keeps the original declaration read selected by its actual
authentication, before the parent substitution. -/
theorem view_original_lookup
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (view : SourceCoreCallableViews.View program plan) :
    ∃ caller original name,
      SourceCompilationPlan.exactSpecialization plan view.owner = .ok caller ∧
      caller.function.typedBody = view.binding.source ∧
      view.binding.source.lookupExpression? view.read = some original ∧
      view.reference.original = original.applySubstitution view.parentActive ∧
      original.form = .reference name (.local view.binding.binder.id) := by
  exact original_lookup view.authenticatedReference

end Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
