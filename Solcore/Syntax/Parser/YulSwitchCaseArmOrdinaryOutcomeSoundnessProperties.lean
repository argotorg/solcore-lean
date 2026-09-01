import Solcore.Syntax.DeclarativeYulSwitchOutcomeGrammar
import Solcore.Syntax.Parser.Yul.Control
import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLookaheadProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable ordinary-success and rejection bridges for one Yul case arm. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

private theorem rejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

private theorem yulLiteral_ne_reject_of_startsYulLiteral
    {input rejected : State} {failure : Failure}
    (starts : startsYulLiteral input = true)
    (result : yulLiteral input = .reject failure rejected) : False := by
  unfold startsYulLiteral State.peekKind? at starts
  unfold yulLiteral at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals contradiction

private theorem yulLiteral_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : yulLiteral input = .reject failure rejected) :
    rejected = input := by
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_rejected_state_eq result }
        all_goals contradiction

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every executable case-arm success follows the ordinary recursive block
relation, independently of diagnostics. -/
theorem caseArm_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {arm : YulCase}
    (result : caseArm statement input = .ok arm output) :
    DeclarativeGrammar.YulCaseArmOrdinaryParses statementOrdinary
      input.declarativeRemainder arm output.declarativeRemainder := by
  unfold caseArm at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, literalStage⟩
  rcases bind_ok_components literalStage with
    ⟨literal, afterLiteral, literalResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .caseKw .yulStatement markerResult)
    (yulLiteral_success_sound literalResult)
    (yulBlock_success_ordinary_sound statement statementOrdinary
      statementSuccessSound bodyResult)

/-- Every executable case-arm rejection identifies its exact sequential
stage and rejected remainder. -/
theorem caseArm_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : caseArm statement input = .reject failure rejected) :
    DeclarativeGrammar.YulCaseArmRejects statementOrdinary statementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold caseArm at result
  cases markerResult : keyword .caseKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .caseKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .caseKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases literalResult : yulLiteral afterMarker with
      | invariant error => simp [literalResult] at result
      | reject literalFailure literalRejected =>
          have rejectedEq := yulLiteral_reject_state_eq literalResult
          subst literalRejected
          simp only [literalResult] at result
          cases result
          exact .literalMissing marker.span
            (keyword_success_exactTokenParses .caseKw .yulStatement
              markerResult)
            (fun starts => yulLiteral_ne_reject_of_startsYulLiteral
              (startsYulLiteral_eq_true_of_yulLiteralStartsAt starts)
              literalResult)
      | ok literal afterLiteral =>
          simp only [literalResult] at result
          cases bodyResult : yulBlock statement afterLiteral with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .caseKw .yulStatement
                  markerResult)
                (yulLiteral_success_sound literalResult)
                (yulBlock_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  bodyResult)
          | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser.YulControl
