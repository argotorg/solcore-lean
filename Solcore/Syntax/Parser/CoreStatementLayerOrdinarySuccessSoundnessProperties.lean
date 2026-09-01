import Solcore.Syntax.Parser.CoreAssemblyStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreForStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementControlLeafOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementIfOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerOrdinarySuccessHelperProperties
import Solcore.Syntax.Parser.CoreStatementSimpleOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementWhileOrdinaryOutcomeSoundnessProperties

/-! Ordinary-success reflection for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

open StatementLayerSuccessInternals

/-- Every executable statement-layer success selects its exact prioritized
ordinary branch, including transactional fallback after a primary rejection. -/
theorem statementLayer_success_ordinary_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
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
    {input output : State} {value : Statement}
    (result : statementLayer nestedStatement expression pattern input =
      .ok value output) :
    DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder value
          output.declarativeRemainder := by
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact selected_guarded_success expression expressionSuccessSound
      expressionRejectSound .letGuard (by simp) .start
        (keyword_guard_of_true .letKw letPresent) (letStatement expression)
          (letStatement_ordinaryOutcome_sound expression expressionOrdinary
            expressionRejects expressionSuccessSound expressionRejectSound)
          result
  · have letFalse : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard := .afterLet .start
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      exact selected_guarded_success expression expressionSuccessSound
        expressionRejectSound .returnGuard (by simp) beforeReturn
          (keyword_guard_of_true .returnKw returnPresent)
          (returnStatement expression)
          (returnStatement_ordinaryOutcome_sound expression expressionOrdinary
            expressionRejects expressionSuccessSound expressionRejectSound)
          result
    · have returnFalse : isKeyword input .returnKw = false :=
        Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard := .afterReturn beforeReturn
        (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        exact selected_guarded_success expression expressionSuccessSound
          expressionRejectSound .matchGuard (by simp) beforeMatch
            (keyword_guard_of_true .matchKw matchPresent)
            (matchStatement nestedStatement expression pattern)
            (matchStatement_ordinaryOutcome_sound nestedStatement expression
              pattern statementOrdinary statementRejects expressionOrdinary
                expressionRejects patternOrdinary patternRejects
                  statementSuccessSound statementRejectSound
                    expressionSuccessSound expressionRejectSound
                      expressionWindow patternSuccessSound patternRejectSound)
            result
      · have matchFalse : isKeyword input .matchKw = false :=
          Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard := .afterMatch beforeMatch
          (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact selected_guarded_success expression expressionSuccessSound
            expressionRejectSound .forGuard (by simp) beforeFor
              (keyword_guard_of_true .forKw forPresent)
              (forStatement nestedStatement expression)
              (forStatement_ordinaryOutcome_sound nestedStatement expression
                statementOrdinary statementRejects expressionRejects
                  expressionOrdinary statementSuccessSound
                    statementRejectSound expressionSuccessSound
                      expressionRejectSound expressionStrict) result
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            exact selected_guarded_success expression expressionSuccessSound
              expressionRejectSound .whileGuard (by simp) beforeWhile
                (contextual_guard_of_true .while whilePresent)
                (whileStatement nestedStatement expression)
                (whileStatement_ordinaryOutcome_sound nestedStatement
                  expression statementOrdinary statementRejects
                    expressionRejects expressionOrdinary statementSuccessSound
                      statementRejectSound expressionSuccessSound
                        expressionRejectSound) result
          · have whileFalse : isContextual input .while = false :=
              Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard := .afterWhile beforeWhile
              (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              exact selected_guarded_success expression expressionSuccessSound
                expressionRejectSound .ifGuard (by simp) beforeIf
                  (keyword_guard_of_true .ifKw ifPresent)
                  (ifStatement nestedStatement expression)
                  (ifStatement_ordinaryOutcome_sound nestedStatement expression
                    statementOrdinary statementRejects expressionRejects
                      expressionOrdinary statementSuccessSound
                        statementRejectSound expressionSuccessSound
                          expressionRejectSound) result
            · have ifFalse : isKeyword input .ifKw = false :=
                Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly : DeclarativeGrammar.StatementLayerPrefixAbsent
                  input.declarativeRemainder .assemblyGuard := .afterIf beforeIf
                (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                exact selected_guarded_success expression expressionSuccessSound
                  expressionRejectSound .assemblyGuard (by simp) beforeAssembly
                    (keyword_guard_of_true .assemblyKw assemblyPresent)
                    assemblyStatement assemblyStatement_ordinaryOutcome_sound
                    result
              · have assemblyFalse : isKeyword input .assemblyKw = false :=
                  Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false]
                  at result
                have beforeBlock : DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  exact selected_guarded_success expression
                    expressionSuccessSound expressionRejectSound .blockGuard
                      (by simp) beforeBlock
                        (symbol_guard_of_true .leftBrace blockPresent)
                        (blockStatement nestedStatement)
                        (blockStatement_ordinaryOutcome_sound nestedStatement
                          statementOrdinary statementRejects
                            statementSuccessSound statementRejectSound) result
                · have blockFalse : isSymbol input .leftBrace = false :=
                    Bool.eq_false_iff.mpr blockPresent
                  simp only [blockFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.StatementLayerPrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterBlock beforeBlock
                      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    exact selected_guarded_success expression
                      expressionSuccessSound expressionRejectSound .breakGuard
                        (by simp) beforeBreak
                          (keyword_guard_of_true .breakKw breakPresent)
                          breakStatement
                          (ControlInternals.terminatedControl_ordinaryOutcome_sound
                            .breakKw .breakStmt) result
                  · have breakFalse : isKeyword input .breakKw = false :=
                      Bool.eq_false_iff.mpr breakPresent
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
                      exact selected_guarded_success expression
                        expressionSuccessSound expressionRejectSound
                          .continueGuard (by simp) beforeContinue
                            (keyword_guard_of_true .continueKw continuePresent)
                            continueStatement
                            (ControlInternals.terminatedControl_ordinaryOutcome_sound
                              .continueKw .continueStmt) result
                    · have continueFalse :
                          isKeyword input .continueKw = false :=
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
                        (assignmentOrExpressionStatement_success_ordinary_sound
                          expression expressionOrdinary expressionSuccessSound
                            result)⟩

end Solcore.Syntax.Parser.TermInternals
