import Solcore.SourceSemantics.SourceInferenceProtectedVariableFrameContracts
import Solcore.SourceSemantics.SourceInferenceProtectedVariablePatterns

/-! A match arm follows its real pattern and body calls, restores the saved
lexical scope, and passes the reached state to the remaining arms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferMatchCasesFuel_cons_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial : State}
    (bodyIH : ∀ state, InferStatementsFuelFixedness protectedVars fuel context
      arm.value.body.value expectedReturn state)
    (tailIH : ∀ body : BlockResult, InferMatchCasesFuelFixedness protectedVars fuel
      context scrutineeType expectedReturn outerScope rest
      (body.state.restoreLexicalScope outerScope)) :
    InferMatchCasesFuelFixedness protectedVars (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial := by
  intro ready wellFormed bound live fixed catalog validated canonical scrutineeBelow
    scrutineeSafe returnBelow returnSafe scopeEq result accepted
  subst outerScope
  unfold inferMatchCasesFuel at accepted
  simp only [bind, Except.bind] at accepted
  cases patternRun : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial with
  | error error => simp [patternRun] at accepted
  | ok patternPair =>
    rcases patternPair with ⟨pattern, patternState⟩
    simp only [patternRun] at accepted
    cases bodyRun : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState with
    | error error => simp [bodyRun] at accepted
    | ok body =>
      simp only [bodyRun] at accepted
      cases tailRun : inferMatchCasesFuel fuel context scrutineeType expectedReturn initial.lexicalScope
          rest (body.state.restoreLexicalScope initial.lexicalScope) with
      | error error => simp [tailRun] at accepted
      | ok tail =>
        simp only [tailRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have patternProperties := inferMatchPatternFuel_inferenceProperties ready
          scrutineeBelow validated patternRun
        have patternPrivacy := inferMatchPatternFuel_private ready scrutineeBelow validated
          bound scrutineeSafe live patternRun
        have patternFixed := inferMatchPatternFuel_fixes_protected ready scrutineeBelow validated
          bound scrutineeSafe live fixed patternRun
        have patternWellFormed := (inferMatchPatternFuel_direct_progress patternRun).wellFormed wellFormed
        have returnAtPattern := returnBelow.weaken patternProperties.1.next_le
        have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
          validated canonical returnAtPattern bodyRun
        have bodyPrivacy := inferStatementsFuel_private protectedVars fuel context arm.value.body.value expectedReturn patternState patternProperties.2.1 patternWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) patternProperties.1.next_le)
          patternPrivacy.2.1 catalog validated canonical returnAtPattern
          (patternPrivacy.1 _ returnSafe) body bodyRun
        have bodyFixed := bodyIH patternState patternProperties.2.1 patternWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) patternProperties.1.next_le)
          patternPrivacy.2.1 patternFixed catalog validated canonical returnAtPattern
          (patternPrivacy.1 _ returnSafe) body bodyRun
        have throughBody := patternProperties.1.trans bodyProperties.1
        have privacyThroughBody := patternPrivacy.1.trans bodyPrivacy.1
        have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
        let restored := body.state.restoreLexicalScope initial.lexicalScope
        have restoredPrivacy : SafeTransport protectedVars body.state restored := .of_substitution_eq rfl
        have privacyThroughRestored := privacyThroughBody.trans restoredPrivacy
        have restoredLive : LiveBindersSafe protectedVars restored := live.restore privacyThroughBody
        have restoredWellFormed : restored.RequirementsWellFormed :=
          State.restoreLexicalScope_preserves_requirementsWellFormed body.state initial.lexicalScope
            ((inferStatementsFuel_direct_progress bodyRun).wellFormed patternWellFormed)
        have tailFixed := tailIH body restoredProperties.2 restoredWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) restoredProperties.1.next_le)
          restoredLive (bodyFixed.of_substitution_eq rfl) catalog validated canonical
          (scrutineeBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ scrutineeSafe)
          (returnBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ returnSafe) (by simp) tail tailRun
        exact tailFixed

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
