import Solcore.Syntax.DeclarativeYulStatementCoreEmbeddingProperties
import Solcore.Syntax.Parser.RecognizedYulStatementFallbackOutcomeProperties
import Solcore.Syntax.Parser.YulBlockStatementOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulForStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulFunctionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulIfStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulLetOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulNameStatementOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulStatementCoreLookaheadProperties
import Solcore.Syntax.Parser.YulStatementCoreOrdinaryTailSoundnessProperties
import Solcore.Syntax.Parser.YulSwitchOrdinaryOutcomeSoundnessProperties

/-! Unconditional ordinary-success reflection for `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

private theorem symbol_guard_of_true (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.YulStatementCoreTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .yulStatement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .yulStatement result).1⟩

private theorem keyword_guard_of_true (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.YulStatementCoreTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .yulStatement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .yulStatement result).1⟩

/-- Every executable core success follows its exact prioritized ordinary
branch, including transactional expression fallback. -/
theorem yulStatementCore_success_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulStatementCore nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
      (yulBlockStatement nested) yulExpressionStatement
      (DeclarativeGrammar.YulBlockStatementOrdinaryParses statementOrdinary)
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      (DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
        statementRejects)
      (yulBlockStatement_success_ordinary_sound nested statementOrdinary
        nestedSuccessSound)
      (yulBlockStatement_reject_ordinary_sound nested statementOrdinary
        statementRejects nestedSuccessSound nestedRejectSound)
      yulExpressionStatement_success_ordinary_sound result
    exact ⟨.blockGuard, .block .start
      (symbol_guard_of_true .leftBrace blockPresent) parsed⟩
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard := .afterBlock .start
      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
        yulLetStatement yulExpressionStatement
        DeclarativeGrammar.YulLetStatementOrdinaryParses
        DeclarativeGrammar.YulExpressionStatementOrdinaryParses
        DeclarativeGrammar.YulLetStatementRejects
        yulLetStatement_success_ordinary_sound yulLetStatement_reject_sound
        yulExpressionStatement_success_ordinary_sound result
      exact ⟨.letGuard, .letDecl beforeLet
        (keyword_guard_of_true .letKw letPresent) parsed⟩
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard := .afterLet beforeLet
        (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
          (yulIfStatement nested) yulExpressionStatement
          (DeclarativeGrammar.YulIfStatementOrdinaryParses statementOrdinary)
          DeclarativeGrammar.YulExpressionStatementOrdinaryParses
          (DeclarativeGrammar.YulIfStatementRejects statementOrdinary
            statementRejects)
          (yulIfStatement_success_ordinary_sound nested statementOrdinary
            nestedSuccessSound)
          (yulIfStatement_reject_ordinary_sound nested statementOrdinary
            statementRejects nestedSuccessSound nestedRejectSound)
          yulExpressionStatement_success_ordinary_sound result
        exact ⟨.ifGuard, .ifThen beforeIf
          (keyword_guard_of_true .ifKw ifPresent) parsed⟩
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard := .afterIf beforeIf
          (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
            (yulForStatement nested) yulExpressionStatement
            (DeclarativeGrammar.YulForStatementOrdinaryParses
              statementOrdinary)
            DeclarativeGrammar.YulExpressionStatementOrdinaryParses
            (DeclarativeGrammar.YulForStatementRejects statementOrdinary
              statementRejects)
            (yulForStatement_success_ordinary_sound nested statementOrdinary
              nestedSuccessSound)
            (yulForStatement_reject_ordinary_sound nested statementOrdinary
              statementRejects nestedSuccessSound nestedRejectSound)
            yulExpressionStatement_success_ordinary_sound result
          exact ⟨.forGuard, .forLoop beforeFor
            (keyword_guard_of_true .forKw forPresent) parsed⟩
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            have parsed :=
              recognizedYulStatementOrFallback_success_ordinary_sound
                (yulSwitchStatement nested) yulExpressionStatement
                (DeclarativeGrammar.YulSwitchStatementOrdinaryParses
                  statementOrdinary)
                DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                (DeclarativeGrammar.YulSwitchStatementRejects
                  statementOrdinary statementRejects)
                (yulSwitchStatement_success_ordinary_sound nested
                  statementOrdinary nestedSuccessSound)
                (yulSwitchStatement_reject_ordinary_sound nested
                  statementOrdinary statementRejects nestedSuccessSound
                    nestedRejectSound)
                yulExpressionStatement_success_ordinary_sound result
            exact ⟨.switchGuard, .switch beforeSwitch
              (keyword_guard_of_true .switchKw switchPresent) parsed⟩
          · have switchFalse : isKeyword input .switchKw = false :=
              Bool.eq_false_iff.mpr switchPresent
            simp only [switchFalse, Bool.false_eq_true, if_false] at result
            have beforeFunction :
                DeclarativeGrammar.YulStatementCorePrefixAbsent
                  input.declarativeRemainder .functionGuard :=
              .afterSwitch beforeSwitch
                (keywordAbsentAt_of_isKeyword_eq_false .switchKw switchFalse)
            by_cases functionPresent : isKeyword input .functionKw
            · simp only [functionPresent, if_true] at result
              have parsed :=
                recognizedYulStatementOrFallback_success_ordinary_sound
                  (yulFunctionStatement nested) yulExpressionStatement
                  (DeclarativeGrammar.YulFunctionStatementOrdinaryParses
                    statementOrdinary)
                  DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                  (DeclarativeGrammar.YulFunctionStatementRejects
                    statementOrdinary statementRejects)
                  (yulFunctionStatement_success_ordinary_sound nested
                    statementOrdinary nestedSuccessSound)
                  (yulFunctionStatement_reject_ordinary_sound nested
                    statementOrdinary statementRejects nestedSuccessSound
                      nestedRejectSound)
                  yulExpressionStatement_success_ordinary_sound result
              exact ⟨.functionGuard, .functionDef beforeFunction
                (keyword_guard_of_true .functionKw functionPresent) parsed⟩
            · have functionFalse : isKeyword input .functionKw = false :=
                Bool.eq_false_iff.mpr functionPresent
              simp only [functionFalse, Bool.false_eq_true, if_false] at result
              have beforeReturn :
                  DeclarativeGrammar.YulStatementCorePrefixAbsent
                    input.declarativeRemainder .returnGuard :=
                .afterFunction beforeFunction
                  (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                    functionFalse)
              by_cases returnPresent : isKeyword input .returnKw
              · simp only [returnPresent, if_true] at result
                have parsed :=
                  recognizedYulStatementOrFallback_success_ordinary_sound
                    yulReturnBuiltin yulExpressionStatement
                    DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
                    DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                    DeclarativeGrammar.YulReturnBuiltinRejects
                    yulReturnBuiltin_success_ordinary_sound
                    yulReturnBuiltin_reject_ordinaryOutcome_sound
                    yulExpressionStatement_success_ordinary_sound result
                exact ⟨.returnGuard, .returnBuiltin beforeReturn
                  (keyword_guard_of_true .returnKw returnPresent) parsed⟩
              · have returnFalse : isKeyword input .returnKw = false :=
                  Bool.eq_false_iff.mpr returnPresent
                simp only [returnFalse, Bool.false_eq_true, if_false] at result
                have beforeLeave :
                    DeclarativeGrammar.YulStatementCorePrefixAbsent
                      input.declarativeRemainder .leaveGuard :=
                  .afterReturn beforeReturn
                    (keywordAbsentAt_of_isKeyword_eq_false .returnKw
                      returnFalse)
                by_cases leavePresent : isKeyword input .leaveKw
                · simp only [leavePresent, if_true] at result
                  have parsed :=
                    recognizedYulStatementOrFallback_success_ordinary_sound
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (DeclarativeGrammar.YulControlTokenOrdinaryParses
                        .leaveKw .leave)
                      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                      (DeclarativeGrammar.YulControlTokenRejects .leaveKw)
                      (yulControlToken_success_ordinary_sound .leaveKw .leave)
                      (yulControlToken_reject_ordinaryOutcome_sound .leaveKw
                        .leave)
                      yulExpressionStatement_success_ordinary_sound result
                  exact ⟨.leaveGuard, .leave beforeLeave
                    (keyword_guard_of_true .leaveKw leavePresent) parsed⟩
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false]
                    at result
                  change yulStatementCoreAfterLeave input =
                    .ok statement output at result
                  exact yulStatementCoreAfterLeave_success_ordinary_sound
                    statementOrdinary statementRejects beforeLeave
                    (keywordAbsentAt_of_isKeyword_eq_false .leaveKw leaveFalse)
                    result

end Solcore.Syntax.Parser
