import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts

/-! Numeric defaulting removes flexible variables. Its real finalization
receipt therefore preserves privacy without requiring the defaulted variable
to be private before defaulting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem default_unifier (v : TypeVarId) :
    Unification.unifyTypes (.variable v) .word = .ok [(v,.word)] := by
  exact Unification.unifyWithFuel_variable_constructor 14 v (.builtin .word)

private theorem unify_word_private {protectedVars : List TypeVarId}
    {before after : State} {original resolved : TypeVarId}
    (normal : before.resolve (.variable original) = .variable resolved)
    (accepted : Detail.unify before (.variable original) .word = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  have unifyEq : before.inference.unify (.variable original) .word =
      .ok { before.inference with substitution := Substitution.compose [(resolved,Ty.word)] before.inference.substitution } := by
    unfold InferState.unify
    change (do
      let update ← Unification.unifyTypes (before.resolve (.variable original)) .word
      pure { before.inference with substitution := update.compose before.inference.substitution }) = _
    simp only [normal,default_unifier,bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [unifyEq,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
  subst after
  have range : Substitution.RangeAvoidsDomain [(resolved,Ty.word)] (guard protectedVars) := by
    intro v type member
    have same : (v,type) = (resolved,Ty.word) := List.mem_singleton.mp member
    cases same
    intro candidate occurs
    simp only [Ty.word,Ty.freeVariables,List.not_mem_nil] at occurs
  intro type safe
  simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

theorem defaultIntegerPatternTarget_private {protectedVars : List TypeVarId}
    {before after : State} {origin : IntegerPatternOrigin}
    (accepted : Detail.defaultIntegerPatternTarget before origin = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.defaultIntegerPatternTarget at accepted
  split at accepted
  · exact unify_word_private (by assumption) accepted
  · have same : before = after := Except.ok.inj accepted
    subst after
    exact .refl _ _

theorem defaultIntegerLiteralTarget_private {protectedVars : List TypeVarId}
    {before after : State} {origin : IntegerLiteralOrigin}
    (accepted : Detail.defaultIntegerLiteralTarget before origin = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.defaultIntegerLiteralTarget at accepted
  split at accepted
  · exact unify_word_private (by assumption) accepted
  · have same : before = after := Except.ok.inj accepted
    subst after
    exact .refl _ _

theorem defaultIntegerPatternTargets_private {protectedVars : List TypeVarId}
    {before after : State} {origins : List IntegerPatternOrigin}
    (accepted : Detail.defaultIntegerPatternTargets origins before = .ok after) :
    SafeTransport protectedVars before after := by
  induction origins generalizing before with
  | nil =>
    cases Except.ok.inj accepted
    exact .refl _ _
  | cons origin rest ih =>
    unfold Detail.defaultIntegerPatternTargets at accepted
    cases head : Detail.defaultIntegerPatternTarget before origin with
    | error error => simp [head,bind,Except.bind] at accepted
    | ok next =>
      simp only [head,bind,Except.bind] at accepted
      exact (defaultIntegerPatternTarget_private head).trans (ih accepted)

theorem defaultIntegerLiteralTargets_private {protectedVars : List TypeVarId}
    {before after : State} {origins : List IntegerLiteralOrigin}
    (accepted : Detail.defaultIntegerLiteralTargets origins before = .ok after) :
    SafeTransport protectedVars before after := by
  induction origins generalizing before with
  | nil =>
    cases Except.ok.inj accepted
    exact .refl _ _
  | cons origin rest ih =>
    unfold Detail.defaultIntegerLiteralTargets at accepted
    cases head : Detail.defaultIntegerLiteralTarget before origin with
    | error error => simp [head,bind,Except.bind] at accepted
    | ok next =>
      simp only [head,bind,Except.bind] at accepted
      exact (defaultIntegerLiteralTarget_private head).trans (ih accepted)

/-- The exact public finalization result preserves every previously private
type. This follows from its two successful defaulting passes. -/
theorem finalize_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : SourceInference.Result}
    (accepted : Detail.finalize context type state roots = .ok result) :
    ∀ value, Safe protectedVars state value → Avoids protectedVars (result.substitution.apply value) := by
  let witness := Detail.finalize_success_witness accepted
  have through : SafeTransport protectedVars state witness.finalState := (defaultIntegerPatternTargets_private witness.patternDefault).trans
    (defaultIntegerLiteralTargets_private witness.literalDefault)
  intro value safe
  have finalSafe := through value safe
  have substEq : result.substitution = witness.finalState.inference.substitution :=
    congrArg SourceInference.Result.substitution witness.result_eq
  rw [substEq]
  exact finalSafe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
