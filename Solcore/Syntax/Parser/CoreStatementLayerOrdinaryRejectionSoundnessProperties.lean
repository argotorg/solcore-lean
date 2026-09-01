import Solcore.Syntax.Parser.CoreAssemblyStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreAssignmentStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreForStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementControlLeafOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementIfOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerOrdinaryRejectionPrimitiveProperties
import Solcore.Syntax.Parser.CoreStatementSimpleOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementWhileOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection for the ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Every executable statement-layer rejection retains the exact selected
guard, its priority prefix, and the transactional fallback rejection. -/
theorem statementLayer_reject_ordinary_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects patternRejects :
      DeclarativeGrammar.Remainder → DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      nestedStatement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      nestedStatement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : statementLayer nestedStatement expression pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.StatementLayerRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  let fallback := assignmentOrExpressionStatement expression
  have fallbackSound : StatementLayerExecutableOutcomeSound fallback
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects) :=
    ⟨assignmentOrExpressionStatement_success_ordinary_sound expression
        expressionOrdinary expressionSuccessSound,
      assignmentOrExpressionStatement_reject_ordinary_sound expression
        expressionOrdinary expressionRejects expressionSuccessSound
          expressionRejectSound⟩
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact statementLayerSelectedGuarded_reject .letGuard (by simp) .start
      (statementLayerKeywordTokenAt_of_isKeyword_eq_true .letKw letPresent)
      (letStatement expression) fallback
      (letStatement_ordinaryOutcome_sound expression expressionOrdinary
        expressionRejects expressionSuccessSound expressionRejectSound)
      fallbackSound result
  · have letFalse := Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard :=
      .afterLet .start (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      exact statementLayerSelectedGuarded_reject .returnGuard (by simp)
        beforeReturn
        (statementLayerKeywordTokenAt_of_isKeyword_eq_true .returnKw
          returnPresent)
        (returnStatement expression) fallback
        (returnStatement_ordinaryOutcome_sound expression expressionOrdinary
          expressionRejects expressionSuccessSound expressionRejectSound)
        fallbackSound result
    · have returnFalse := Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard := .afterReturn beforeReturn
        (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        exact statementLayerSelectedGuarded_reject .matchGuard (by simp)
          beforeMatch
          (statementLayerKeywordTokenAt_of_isKeyword_eq_true .matchKw
            matchPresent)
          (matchStatement nestedStatement expression pattern) fallback
          (matchStatement_ordinaryOutcome_sound nestedStatement expression
            pattern statementOrdinary statementRejects expressionOrdinary
            expressionRejects patternOrdinary patternRejects
            statementSuccessSound statementRejectSound expressionSuccessSound
            expressionRejectSound expressionWindow patternSuccessSound
            patternRejectSound) fallbackSound result
      · have matchFalse := Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard := .afterMatch beforeMatch
          (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact statementLayerSelectedGuarded_reject .forGuard (by simp)
            beforeFor
            (statementLayerKeywordTokenAt_of_isKeyword_eq_true .forKw
              forPresent)
            (forStatement nestedStatement expression) fallback
            (forStatement_ordinaryOutcome_sound nestedStatement expression
              statementOrdinary statementRejects expressionRejects
              expressionOrdinary statementSuccessSound statementRejectSound
              expressionSuccessSound expressionRejectSound expressionStrict)
            fallbackSound result
        · have forFalse := Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            exact statementLayerSelectedGuarded_reject .whileGuard (by simp)
              beforeWhile
              (statementLayerContextualTokenAt_of_isContextual_eq_true .while
                whilePresent)
              (whileStatement nestedStatement expression) fallback
              (whileStatement_ordinaryOutcome_sound nestedStatement expression
                statementOrdinary statementRejects expressionRejects
                expressionOrdinary statementSuccessSound statementRejectSound
                expressionSuccessSound expressionRejectSound)
              fallbackSound result
          · have whileFalse := Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard := .afterWhile beforeWhile
              (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              exact statementLayerSelectedGuarded_reject .ifGuard (by simp)
                beforeIf
                (statementLayerKeywordTokenAt_of_isKeyword_eq_true .ifKw
                  ifPresent)
                (ifStatement nestedStatement expression) fallback
                (ifStatement_ordinaryOutcome_sound nestedStatement expression
                  statementOrdinary statementRejects expressionRejects
                  expressionOrdinary statementSuccessSound statementRejectSound
                  expressionSuccessSound expressionRejectSound)
                fallbackSound result
            · have ifFalse := Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly :
                  DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .assemblyGuard :=
                .afterIf beforeIf
                  (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                exact statementLayerSelectedGuarded_reject .assemblyGuard
                  (by simp) beforeAssembly
                  (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                    .assemblyKw assemblyPresent)
                  assemblyStatement fallback
                  assemblyStatement_ordinaryOutcome_sound fallbackSound result
              · have assemblyFalse := Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false]
                  at result
                have beforeBlock :
                    DeclarativeGrammar.StatementLayerPrefixAbsent
                      input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  exact statementLayerSelectedGuarded_reject .blockGuard
                    (by simp) beforeBlock
                    (statementLayerSymbolTokenAt_of_isSymbol_eq_true .leftBrace
                      blockPresent)
                    (blockStatement nestedStatement) fallback
                    (blockStatement_ordinaryOutcome_sound nestedStatement
                      statementOrdinary statementRejects statementSuccessSound
                      statementRejectSound) fallbackSound result
                · have blockFalse := Bool.eq_false_iff.mpr blockPresent
                  simp only [blockFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.StatementLayerPrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterBlock beforeBlock
                      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    exact statementLayerSelectedGuarded_reject .breakGuard
                      (by simp) beforeBreak
                      (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                        .breakKw breakPresent)
                      breakStatement fallback
                      (ControlInternals.terminatedControl_ordinaryOutcome_sound .breakKw
                        .breakStmt) fallbackSound result
                  · have breakFalse := Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.StatementLayerPrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      exact statementLayerSelectedGuarded_reject .continueGuard
                        (by simp) beforeContinue
                        (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                          .continueKw continuePresent)
                        continueStatement fallback
                        (ControlInternals.terminatedControl_ordinaryOutcome_sound .continueKw
                          .continueStmt) fallbackSound result
                    · have continueFalse :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeFallback :
                          DeclarativeGrammar.StatementLayerPrefixAbsent
                            input.declarativeRemainder .fallback :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      exact ⟨.fallback, .fallback beforeFallback
                        (fallbackSound.2 result)⟩

end Solcore.Syntax.Parser.TermInternals
