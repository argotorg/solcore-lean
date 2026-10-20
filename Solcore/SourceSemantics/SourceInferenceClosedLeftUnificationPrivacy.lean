import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyFinalization
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization
import Solcore.SourceSemantics.SourceInferenceGeneralizedActualStateInvariant

/-! Unifying a closed left operand can only remove flexible variables. Bare
returns use this actual update even when a lambda return type is fresh. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem apply_closed (substitution : Substitution) {type : Ty}
    (closed : type.VariablesBelow 0) : substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type
    (fun v _ occurs => False.elim (Nat.not_lt_zero _ (closed v occurs)))

private theorem closed_left_range {left right : Ty} {substitution : Substitution}
    (closed : left.VariablesBelow 0)
    (accepted : Unification.unifyTypes left right = .ok substitution) :
    ∀ v replacement, (v,replacement) ∈ substitution → replacement.VariablesBelow 0 := by
  have matched : substitution.apply right = left :=
    (Unification.unifyTypes_sound accepted).symm.trans (apply_closed substitution closed)
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) accepted
  intro v replacement member candidate occurs
  have inDomain : v ∈ substitution.domain := List.mem_map.mpr ⟨(v,replacement),member,rfl⟩
  obtain ⟨constraint,present,origin⟩ := Unification.unify_domain_origin accepted inDomain
  have same : constraint = { left, right } := List.mem_singleton.mp present
  subst constraint
  have rightOrigin : v ∈ right.freeVariables := origin.resolve_left
    (fun occurs => Nat.not_lt_zero _ (closed v occurs))
  have found := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have image : candidate ∈ (substitution.apply (.variable v)).freeVariables := by
    simpa only [Substitution.apply,found,Option.getD_some] using occurs
  have inResult := MonomorphicGeneralization.replacement_occurs substitution right rightOrigin image
  rw [matched] at inResult
  exact closed candidate inResult

/-- Successful unification with a left operand containing no flexible
variables can only remove flexible variables from other live types. -/
theorem unify_closed_left_private {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (closed : left.VariablesBelow 0)
    (accepted : Detail.unify before left right = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    have sameLeft : before.inference.resolve left = left := apply_closed _ closed
    rw [sameLeft] at unified
    cases update : Unification.unifyTypes left (before.inference.resolve right) with
    | error error => simp [update,bind,Except.bind] at unified
    | ok substitution =>
      simp only [update,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at unified
      cases unified
      have range : substitution.RangeAvoidsDomain (guard protectedVars) := by
        intro v replacement member candidate occurs
        exact False.elim (Nat.not_lt_zero _ (closed_left_range closed update v replacement member candidate occurs))
      intro type safe
      simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.unifyClosedLeft
    {before after : State} {source : TypedSource} {left right : Ty}
    (invariant : GeneralizedActualStateInvariant before source)
    (ready : before.InferenceReady)
    (closed : left.VariablesBelow 0)
    (rightBelow : right.VariablesBelow before.inference.next)
    (accepted : Detail.unify before left right = .ok after) :
    GeneralizedActualStateInvariant after source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have progress := Detail.unify_inferenceProgress ready.solved
    (closed.weaken (Nat.zero_le _)) rightBelow accepted
  have binders : after.localBinders = before.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
  refine ⟨⟨pending, ledger.unify accepted⟩, invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders progress.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member) ?_ progress.substitution_extends⟩
  · intro binder member
    exact (invariant.privacy binder (binders ▸ member)).transport binders
      (unify_closed_left_private closed accepted)
  · rw [Detail.unify_requirements_eq accepted]
    exact List.Subset.refl _

end Solcore.SourceSemantics.SourceInferenceSoundness
