import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContinuation

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

/-- The current substitution leaves the protected variables themselves fixed.
This is stronger than preservation of types which avoid those variables. -/
def FixesProtected (protectedVars : List TypeVarId) (state : State) : Prop :=
  ∀ q ∈ protectedVars, state.resolve (.variable q) = .variable q

theorem FixesProtected.of_substitution_eq
    {protectedVars : List TypeVarId} {before after : State}
    (fixed : FixesProtected protectedVars before)
    (same : after.inference.substitution = before.inference.substitution) :
    FixesProtected protectedVars after := by
  simpa only [FixesProtected, State.resolve, InferState.resolve, same] using fixed

theorem unify_fixes_protected {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (fixed : FixesProtected protectedVars before)
    (leftSafe : Safe protectedVars before left)
    (rightSafe : Safe protectedVars before right)
    (accepted : Detail.unify before left right = .ok after) :
    FixesProtected protectedVars after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    cases update : Unification.unifyTypes (before.inference.resolve left)
        (before.inference.resolve right) with
    | error error => simp [update, bind, Except.bind] at unified
    | ok substitution =>
      simp only [update, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at unified
      cases unified
      intro q member
      have outside : q ∉ substitution.domain := by
        intro present
        obtain ⟨constraint, origin, occurs⟩ := Unification.unify_domain_origin update present
        have same : constraint = { left := before.inference.resolve left, right := before.inference.resolve right } :=
          List.mem_singleton.mp origin
        subst constraint
        rcases occurs with inLeft | inRight
        · exact leftSafe q inLeft member
        · exact rightSafe q inRight member
      have beforeFixed := fixed q member
      change (substitution.compose before.inference.substitution).apply (.variable q) = .variable q
      rw [Substitution.compose_apply]
      change substitution.apply (before.resolve (.variable q)) = .variable q
      rw [beforeFixed]
      simp only [Substitution.apply, (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside,
        Option.getD_none]

theorem withExpected_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (fixed : FixesProtected protectedVars state)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    FixesProtected protectedVars result.state := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fixed
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact unify_fixes_protected fixed actualSafe expectedSafe (by
        simp [Detail.unify, unified, Detail.liftUnification, bind, Except.bind])
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            intro q member
            simpa only [Detail.commitCoercionPlan_resolve] using fixed q member

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
