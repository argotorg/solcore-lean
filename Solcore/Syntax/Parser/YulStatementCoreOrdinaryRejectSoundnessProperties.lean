import Solcore.Syntax.Parser.YulStatementCoreOrdinarySuccessSoundnessProperties

/-! Exact ordinary-rejection reflection for `yulStatementCore`. -/

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

/-- Every executable core rejection identifies the exact selected branch and
retains both transactional branch rejections. -/
theorem yulStatementCore_reject_ordinary_sound
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
    {input rejected : State} {failure : Failure}
    (result : yulStatementCore nested input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementCoreRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    exact ⟨.blockGuard, .block .start
      (symbol_guard_of_true .leftBrace blockPresent)
      (recognizedYulStatementOrFallback_reject_sound
        (yulBlockStatement nested) yulExpressionStatement
        (DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
          statementRejects)
        DeclarativeGrammar.YulExpressionStatementRejects
        (yulBlockStatement_reject_ordinary_sound nested statementOrdinary
          statementRejects nestedSuccessSound nestedRejectSound)
        yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard := .afterBlock .start
      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      exact ⟨.letGuard, .letDecl beforeLet
        (keyword_guard_of_true .letKw letPresent)
        (recognizedYulStatementOrFallback_reject_sound yulLetStatement
          yulExpressionStatement DeclarativeGrammar.YulLetStatementRejects
          DeclarativeGrammar.YulExpressionStatementRejects
          yulLetStatement_reject_sound
          yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard := .afterLet beforeLet
        (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        exact ⟨.ifGuard, .ifThen beforeIf
          (keyword_guard_of_true .ifKw ifPresent)
          (recognizedYulStatementOrFallback_reject_sound
            (yulIfStatement nested) yulExpressionStatement
            (DeclarativeGrammar.YulIfStatementRejects statementOrdinary
              statementRejects)
            DeclarativeGrammar.YulExpressionStatementRejects
            (yulIfStatement_reject_ordinary_sound nested statementOrdinary
              statementRejects nestedSuccessSound nestedRejectSound)
            yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard := .afterIf beforeIf
          (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact ⟨.forGuard, .forLoop beforeFor
            (keyword_guard_of_true .forKw forPresent)
            (recognizedYulStatementOrFallback_reject_sound
              (yulForStatement nested) yulExpressionStatement
              (DeclarativeGrammar.YulForStatementRejects statementOrdinary
                statementRejects)
              DeclarativeGrammar.YulExpressionStatementRejects
              (yulForStatement_reject_ordinary_sound nested statementOrdinary
                statementRejects nestedSuccessSound nestedRejectSound)
              yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            exact ⟨.switchGuard, .switch beforeSwitch
              (keyword_guard_of_true .switchKw switchPresent)
              (recognizedYulStatementOrFallback_reject_sound
                (yulSwitchStatement nested) yulExpressionStatement
                (DeclarativeGrammar.YulSwitchStatementRejects
                  statementOrdinary statementRejects)
                DeclarativeGrammar.YulExpressionStatementRejects
                (yulSwitchStatement_reject_ordinary_sound nested
                  statementOrdinary statementRejects nestedSuccessSound
                    nestedRejectSound)
                yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
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
              exact ⟨.functionGuard, .functionDef beforeFunction
                (keyword_guard_of_true .functionKw functionPresent)
                (recognizedYulStatementOrFallback_reject_sound
                  (yulFunctionStatement nested) yulExpressionStatement
                  (DeclarativeGrammar.YulFunctionStatementRejects
                    statementOrdinary statementRejects)
                  DeclarativeGrammar.YulExpressionStatementRejects
                  (yulFunctionStatement_reject_ordinary_sound nested
                    statementOrdinary statementRejects nestedSuccessSound
                      nestedRejectSound)
                  yulExpressionStatement_reject_ordinaryOutcome_sound
                    result)⟩
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
                exact ⟨.returnGuard, .returnBuiltin beforeReturn
                  (keyword_guard_of_true .returnKw returnPresent)
                  (recognizedYulStatementOrFallback_reject_sound
                    yulReturnBuiltin yulExpressionStatement
                    DeclarativeGrammar.YulReturnBuiltinRejects
                    DeclarativeGrammar.YulExpressionStatementRejects
                    yulReturnBuiltin_reject_ordinaryOutcome_sound
                    yulExpressionStatement_reject_ordinaryOutcome_sound
                      result)⟩
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
                  exact ⟨.leaveGuard, .leave beforeLeave
                    (keyword_guard_of_true .leaveKw leavePresent)
                    (recognizedYulStatementOrFallback_reject_sound
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (DeclarativeGrammar.YulControlTokenRejects .leaveKw)
                      DeclarativeGrammar.YulExpressionStatementRejects
                      (yulControlToken_reject_ordinaryOutcome_sound .leaveKw
                        .leave)
                      yulExpressionStatement_reject_ordinaryOutcome_sound
                        result)⟩
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false]
                    at result
                  change yulStatementCoreAfterLeave input =
                    .reject failure rejected at result
                  exact yulStatementCoreAfterLeave_reject_ordinary_sound
                    statementOrdinary statementRejects beforeLeave
                    (keywordAbsentAt_of_isKeyword_eq_false .leaveKw leaveFalse)
                    result

end Solcore.Syntax.Parser
