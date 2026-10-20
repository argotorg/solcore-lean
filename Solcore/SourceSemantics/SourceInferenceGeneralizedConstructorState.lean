import Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.freshConstructor
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source)
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) :
    GeneralizedActualStateInvariant
      (Detail.freshDataConstructorInstantiation dataType constructor state).2 source := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldPreserves (parameters : List TypeParameterId) (accumulator : List Ty × State)
      (valid : GeneralizedActualStateInvariant accumulator.2 source) :
      GeneralizedActualStateInvariant (parameters.foldl step accumulator).2 source := by
    induction parameters generalizing accumulator with
    | nil => exact valid
    | cons parameter parameters induction =>
      exact induction (step accumulator parameter) valid.fresh
  exact foldPreserves dataType.parameters ([], state) invariant

private theorem unify_rows {state after : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok after) :
    after.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

theorem GeneralizedActualStateInvariant.unify
    {state after : State} {source : TypedSource} {left right : Ty}
    (invariant : GeneralizedActualStateInvariant state source)
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state left)
    (rightSafe : ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state right)
    (accepted : Detail.unify state left right = .ok after) :
    GeneralizedActualStateInvariant after source := by
  have progress := Detail.unify_inferenceProgress ready.solved leftBelow rightBelow accepted
  have binders : after.localBinders = state.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.unify accepted⟩, invariant.origins.unify accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders progress.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (fun _ member => (unify_rows accepted).symm ▸ member) progress.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (invariant.privacy binder old).unify (leftSafe binder old) (rightSafe binder old) accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
