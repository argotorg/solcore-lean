import Solcore.SourceSemantics.SourceInferenceStatementLedgerInvariant

/-!
Canonical requirement/template ledgers through source-ordered match arms.
Pattern traversal is kept as an explicit smaller-fuel operation here; its
own structural proof lives in a disjoint module.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- An actual match-arm traversal preserves an arbitrary ambient pending
template suffix when the exact smaller-fuel pattern, body, and remaining-arm
calls preserve it.  Pattern-local binders are discarded lexically, but global
requirement rows are retained. -/
theorem inferMatchCasesFuelLedgerPreservation_step
    {fuel : Nat}
    (patternIH : ∀ {context : Frontend.SourceInference.Context}
      {pattern : Syntax.Pattern} {expected : Ty}
      {initial final : State} {inferred : TypedMatchPattern}
      {pending : List RequirementId},
      Detail.inferMatchPatternFuel fuel context pattern expected initial =
        .ok (inferred, final) →
      RecursiveLedgerInvariant initial pending →
      RecursiveLedgerInvariant final pending)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel)
    (casesIH : InferMatchCasesFuelLedgerPreservation fuel) :
    InferMatchCasesFuelLedgerPreservation (fuel + 1) := by
  intro context scrutineeType expectedReturn outerScope cases initial result
    pending success tracked
  cases cases with
  | nil =>
      unfold Detail.inferMatchCasesFuel at success
      injection success with resultEq
      subst result
      exact tracked
  | cons arm rest =>
      unfold Detail.inferMatchCasesFuel at success
      cases patternSuccess : Detail.inferMatchPatternFuel fuel context
          arm.value.pattern scrutineeType initial with
      | error error =>
          simp [patternSuccess, bind, Except.bind] at success
      | ok patternPair =>
          rcases patternPair with ⟨pattern, patternState⟩
          simp only [patternSuccess, bind, Except.bind] at success
          cases bodySuccess : Detail.inferStatementsFuel fuel context
              arm.value.body.value expectedReturn patternState with
          | error error =>
              simp [bodySuccess] at success
          | ok body =>
              simp only [bodySuccess] at success
              cases tailSuccess : Detail.inferMatchCasesFuel fuel context
                  scrutineeType expectedReturn outerScope rest
                  (body.state.restoreLexicalScope outerScope) with
              | error error =>
                  simp [tailSuccess] at success
              | ok tail =>
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  have tailTracked := casesIH tailSuccess
                    ((statementsIH bodySuccess
                      (patternIH patternSuccess tracked)
                    ).restoreLexicalScope outerScope)
                  cases resultEq
                  exact tailTracked

end Solcore.SourceSemantics.SourceInferenceSoundness
