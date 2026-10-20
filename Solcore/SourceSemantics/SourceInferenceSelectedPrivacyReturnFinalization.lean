import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyFinalization
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization
import Solcore.SourceSemantics.SourceCompiledSelectedInferenceProgress

/-! Actual return unification against the declared closed signature and the
actual finalizer preserve private variables, including generalized locals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem apply_closed (substitution : Substitution) {type : Ty}
    (closed : type.VariablesBelow 0) : substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type
    (fun v _ occurs => False.elim (Nat.not_lt_zero _ (closed v occurs)))

private theorem closed_right_range {left right : Ty} {substitution : Substitution}
    (closed : right.VariablesBelow 0)
    (accepted : Unification.unifyTypes left right = .ok substitution) :
    ∀ v replacement, (v,replacement) ∈ substitution → replacement.VariablesBelow 0 := by
  have matched : substitution.apply left = right :=
    (Unification.unifyTypes_sound accepted).trans (apply_closed substitution closed)
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) accepted
  intro v replacement member candidate occurs
  have inDomain : v ∈ substitution.domain := List.mem_map.mpr ⟨(v,replacement),member,rfl⟩
  obtain ⟨constraint,present,origin⟩ := Unification.unify_domain_origin accepted inDomain
  have same : constraint = { left, right } := List.mem_singleton.mp present
  subst constraint
  have leftOrigin : v ∈ left.freeVariables := origin.resolve_right
    (fun occurs => Nat.not_lt_zero _ (closed v occurs))
  have found := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have image : candidate ∈ (substitution.apply (.variable v)).freeVariables := by
    simpa only [Substitution.apply,found,Option.getD_some] using occurs
  have inResult := MonomorphicGeneralization.replacement_occurs substitution left leftOrigin image
  rw [matched] at inResult
  exact closed candidate inResult

/-- Successful unification with a declared type containing no flexible
variables can only remove flexible variables from other live types. -/
theorem unify_closed_right_private {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (closed : right.VariablesBelow 0)
    (accepted : Detail.unify before left right = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    have sameRight : before.inference.resolve right = right := apply_closed _ closed
    rw [sameRight] at unified
    cases update : Unification.unifyTypes (before.inference.resolve left) right with
    | error error => simp [update,bind,Except.bind] at unified
    | ok substitution =>
      simp only [update,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at unified
      cases unified
      have range : substitution.RangeAvoidsDomain (guard protectedVars) := by
        intro v replacement member candidate occurs
        exact False.elim (Nat.not_lt_zero _ (closed_right_range closed update v replacement member candidate occurs))
      intro type safe
      simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- A selected actual checker receipt supplies the closed return signature,
its successful unification and its finalizer. No return-type privacy or
post-defaulting transport law is requested from the caller. -/
theorem Selected.finishPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (protectedVars : List TypeVarId) :
    ∀ type, Safe protectedVars selected.body.body.state type →
      Avoids protectedVars (selected.body.finalized.substitution.apply type) := by
  have formation := Frontend.checkProgram_success_signature_formation checked
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow 0)
  have returned : SafeTransport protectedVars selected.body.body.state selected.body.returned :=
    unify_closed_right_private closed selected.body.unified
  intro type safe
  exact finalize_private selected.body.finalization type (returned type safe)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
