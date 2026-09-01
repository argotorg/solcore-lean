import Solcore.Syntax.DeclarativeYulStatementCoreEmbeddingProperties
import Solcore.Syntax.Parser.RecognizedYulStatementFallbackOutcomeProperties
import Solcore.Syntax.Parser.YulNameStatementOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulStatementCoreLookaheadProperties

/-! Executable ordinary outcomes for the suffix after the `leave` guard. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The exact executable suffix of `yulStatementCore` after a false `leave`
guard. -/
def yulStatementCoreAfterLeave : Parser YulStmt := fun state =>
  let fallback := yulExpressionStatement
  if isKeyword state .breakKw then
    recognizedYulStatementOrFallback
      (yulControlToken .breakKw .break) fallback state
  else if isKeyword state .continueKw then
    recognizedYulStatementOrFallback
      (yulControlToken .continueKw .continue) fallback state
  else if startsYulName state then
    orElse yulAssignment fallback state
  else
    fallback state

private theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, ↓reduceIte]

private theorem keyword_guard_of_true (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.YulStatementCoreTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .yulStatement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .yulStatement result).1⟩

/-- Every successful suffix execution selects its exact ordinary core branch. -/
theorem yulStatementCoreAfterLeave_success_ordinary_sound
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input output : State} {statement : YulStmt}
    (beforeLeave : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .leaveGuard)
    (leaveAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword .leaveKw))
    (result : yulStatementCoreAfterLeave input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementCoreAfterLeave at result
  have beforeBreak : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .breakGuard :=
    .afterLeave beforeLeave leaveAbsent
  by_cases breakPresent : isKeyword input .breakKw
  · simp only [breakPresent, if_true] at result
    have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
      (yulControlToken .breakKw .break) yulExpressionStatement
      (DeclarativeGrammar.YulControlTokenOrdinaryParses .breakKw .break)
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      (DeclarativeGrammar.YulControlTokenRejects .breakKw)
      (yulControlToken_success_ordinary_sound .breakKw .break)
      (yulControlToken_reject_ordinaryOutcome_sound .breakKw .break)
      yulExpressionStatement_success_ordinary_sound result
    exact ⟨.breakGuard, .break beforeBreak
      (keyword_guard_of_true .breakKw breakPresent) parsed⟩
  · have breakFalse : isKeyword input .breakKw = false :=
      Bool.eq_false_iff.mpr breakPresent
    simp only [breakFalse, Bool.false_eq_true, if_false] at result
    have beforeContinue : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .continueGuard := .afterBreak beforeBreak
      (keywordAbsentAt_of_isKeyword_eq_false .breakKw breakFalse)
    by_cases continuePresent : isKeyword input .continueKw
    · simp only [continuePresent, if_true] at result
      have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
        (yulControlToken .continueKw .continue) yulExpressionStatement
        (DeclarativeGrammar.YulControlTokenOrdinaryParses
          .continueKw .continue)
        DeclarativeGrammar.YulExpressionStatementOrdinaryParses
        (DeclarativeGrammar.YulControlTokenRejects .continueKw)
        (yulControlToken_success_ordinary_sound .continueKw .continue)
        (yulControlToken_reject_ordinaryOutcome_sound .continueKw .continue)
        yulExpressionStatement_success_ordinary_sound result
      exact ⟨.continueGuard, .continue beforeContinue
        (keyword_guard_of_true .continueKw continuePresent) parsed⟩
    · have continueFalse : isKeyword input .continueKw = false :=
        Bool.eq_false_iff.mpr continuePresent
      simp only [continueFalse, Bool.false_eq_true, if_false] at result
      have beforeName : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .nameGuard :=
        .afterContinue beforeContinue
          (keywordAbsentAt_of_isKeyword_eq_false .continueKw continueFalse)
      by_cases namePresent : startsYulName input
      · simp only [namePresent, if_true] at result
        exact ⟨.nameGuard, .nameChoice beforeName
          (yulNameStartAt_of_startsYulName_eq_true namePresent)
          (yulNameStatementChoice_success_ordinary_sound result)⟩
      · have nameFalse : startsYulName input = false :=
          Bool.eq_false_iff.mpr namePresent
        simp only [nameFalse, Bool.false_eq_true, if_false] at result
        exact ⟨.fallback, .expressionFallback
          (.afterName beforeName
            (yulNameStartAbsentAt_of_startsYulName_eq_false nameFalse))
          (yulExpressionStatement_success_ordinary_sound result)⟩

/-- Every suffix rejection selects its exact both-rejected core branch. -/
theorem yulStatementCoreAfterLeave_reject_ordinary_sound
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input rejected : State} {failure : Failure}
    (beforeLeave : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .leaveGuard)
    (leaveAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword .leaveKw))
    (result : yulStatementCoreAfterLeave input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementCoreRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulStatementCoreAfterLeave at result
  have beforeBreak : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .breakGuard :=
    .afterLeave beforeLeave leaveAbsent
  by_cases breakPresent : isKeyword input .breakKw
  · simp only [breakPresent, if_true] at result
    exact ⟨.breakGuard, .break beforeBreak
      (keyword_guard_of_true .breakKw breakPresent)
      (recognizedYulStatementOrFallback_reject_sound
        (yulControlToken .breakKw .break) yulExpressionStatement
        (DeclarativeGrammar.YulControlTokenRejects .breakKw)
        DeclarativeGrammar.YulExpressionStatementRejects
        (yulControlToken_reject_ordinaryOutcome_sound .breakKw .break)
        yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
  · have breakFalse : isKeyword input .breakKw = false :=
      Bool.eq_false_iff.mpr breakPresent
    simp only [breakFalse, Bool.false_eq_true, if_false] at result
    have beforeContinue : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .continueGuard := .afterBreak beforeBreak
      (keywordAbsentAt_of_isKeyword_eq_false .breakKw breakFalse)
    by_cases continuePresent : isKeyword input .continueKw
    · simp only [continuePresent, if_true] at result
      exact ⟨.continueGuard, .continue beforeContinue
        (keyword_guard_of_true .continueKw continuePresent)
        (recognizedYulStatementOrFallback_reject_sound
          (yulControlToken .continueKw .continue) yulExpressionStatement
          (DeclarativeGrammar.YulControlTokenRejects .continueKw)
          DeclarativeGrammar.YulExpressionStatementRejects
          (yulControlToken_reject_ordinaryOutcome_sound .continueKw .continue)
          yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
    · have continueFalse : isKeyword input .continueKw = false :=
        Bool.eq_false_iff.mpr continuePresent
      simp only [continueFalse, Bool.false_eq_true, if_false] at result
      have beforeName : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .nameGuard :=
        .afterContinue beforeContinue
          (keywordAbsentAt_of_isKeyword_eq_false .continueKw continueFalse)
      by_cases namePresent : startsYulName input
      · simp only [namePresent, if_true] at result
        exact ⟨.nameGuard, .nameChoice beforeName
          (yulNameStartAt_of_startsYulName_eq_true namePresent)
          (yulNameStatementChoice_reject_sound result)⟩
      · have nameFalse : startsYulName input = false :=
          Bool.eq_false_iff.mpr namePresent
        simp only [nameFalse, Bool.false_eq_true, if_false] at result
        exact ⟨.fallback, .expressionFallback
          (.afterName beforeName
            (yulNameStartAbsentAt_of_startsYulName_eq_false nameFalse))
          (yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩

end Solcore.Syntax.Parser
