import Solcore.Syntax.DeclarativeCoreStatementLayerGrammar
import Solcore.Syntax.Parser.CoreAssemblyStatementSoundnessProperties
import Solcore.Syntax.Parser.CoreAssignmentStatementSoundnessProperties
import Solcore.Syntax.Parser.CoreForStatementSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchStatementSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementControlSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerDiagnosticReflectionProperties

/-! Exact diagnostic-free soundness for the Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Every clean statement-layer success follows its exact prioritized branch. -/
theorem statementLayer_success_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (yulBodyParses : DeclarativeGrammar.Remainder → SourceSpan →
      List YulStmt → DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nestedStatement)
    (nestedSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → nestedStatement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionShape : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (patternSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → pattern input = .ok value next →
      patternParses input.declarativeRemainder value next.declarativeRemainder)
    (yulBodySound : ∀ {input next : State} {body : YulParsedBlock},
      next.diagnosticsRev = [] → yulBody input = .ok body next →
      yulBodyParses input.declarativeRemainder body.span body.body
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : statementLayer nestedStatement expression pattern input =
      .ok value next) :
    DeclarativeGrammar.StatementLayerParses statementParses expressionParses
      patternParses yulBodyParses input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    have primary := recognizedStatementOrFallback_primary_of_diagnosticFree_success
      (letStatement expression) (assignmentOrExpressionStatement expression)
        result diagnosticFree
    exact .letBranch .start (letStatement_success_sound expression
      expressionParses expressionSound diagnosticFree primary)
  · have letFalse : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard :=
      .afterLet .start (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      have primary :=
        recognizedStatementOrFallback_primary_of_diagnosticFree_success
          (returnStatement expression)
            (assignmentOrExpressionStatement expression) result diagnosticFree
      exact .returnBranch beforeReturn (returnStatement_success_sound
        expression expressionParses expressionSound diagnosticFree primary)
    · have returnFalse : isKeyword input .returnKw = false :=
        Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard :=
        .afterReturn beforeReturn
          (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        have primary :=
          recognizedStatementOrFallback_primary_of_diagnosticFree_success
            (matchStatement nestedStatement expression pattern)
              (assignmentOrExpressionStatement expression) result
                diagnosticFree
        exact .matchBranch beforeMatch (matchStatement_success_sound
          nestedStatement expression pattern statementParses expressionParses
            patternParses nestedReflects nestedSound expressionReflects
              expressionSound expressionShape patternReflects patternSound
                diagnosticFree primary)
      · have matchFalse : isKeyword input .matchKw = false :=
          Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard :=
          .afterMatch beforeMatch
            (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have primary :=
            recognizedStatementOrFallback_primary_of_diagnosticFree_success
              (forStatement nestedStatement expression)
                (assignmentOrExpressionStatement expression) result
                  diagnosticFree
          exact .forBranch beforeFor (forStatement_success_sound
            nestedStatement expression statementParses expressionParses
              nestedReflects nestedSound expressionReflects expressionSound
                expressionStrict diagnosticFree primary)
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard :=
            .afterFor beforeFor
              (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            have primary :=
              recognizedStatementOrFallback_primary_of_diagnosticFree_success
                (whileStatement nestedStatement expression)
                  (assignmentOrExpressionStatement expression) result
                    diagnosticFree
            exact .whileBranch beforeWhile (whileStatement_success_sound
              nestedStatement expression statementParses expressionParses
                nestedReflects nestedSound expressionSound diagnosticFree
                  primary)
          · have whileFalse : isContextual input .while = false :=
              Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard :=
              .afterWhile beforeWhile
                (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              have primary :=
                recognizedStatementOrFallback_primary_of_diagnosticFree_success
                  (ifStatement nestedStatement expression)
                    (assignmentOrExpressionStatement expression) result
                      diagnosticFree
              exact .ifBranch beforeIf (ifStatement_success_sound
                nestedStatement expression statementParses expressionParses
                  nestedReflects nestedSound expressionSound diagnosticFree
                    primary)
            · have ifFalse : isKeyword input .ifKw = false :=
                Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly :
                  DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .assemblyGuard :=
                .afterIf beforeIf
                  (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                have primary :=
                  recognizedStatementOrFallback_primary_of_diagnosticFree_success
                    assemblyStatement (assignmentOrExpressionStatement expression)
                      result diagnosticFree
                exact .assemblyBranch beforeAssembly
                  (assemblyStatement_success_sound yulBodyParses yulBodySound
                    diagnosticFree primary)
              · have assemblyFalse : isKeyword input .assemblyKw = false :=
                  Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false] at result
                have beforeBlock :
                    DeclarativeGrammar.StatementLayerPrefixAbsent
                      input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  have primary :=
                    recognizedStatementOrFallback_primary_of_diagnosticFree_success
                      (blockStatement nestedStatement)
                        (assignmentOrExpressionStatement expression) result
                          diagnosticFree
                  exact .blockBranch beforeBlock (blockStatement_success_sound
                    nestedStatement statementParses nestedReflects nestedSound
                      diagnosticFree primary)
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
                    have primary :=
                      recognizedStatementOrFallback_primary_of_diagnosticFree_success
                        breakStatement
                          (assignmentOrExpressionStatement expression) result
                            diagnosticFree
                    exact .breakBranch beforeBreak
                      (breakStatement_success_sound primary)
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
                      have primary :=
                        recognizedStatementOrFallback_primary_of_diagnosticFree_success
                          continueStatement
                            (assignmentOrExpressionStatement expression) result
                              diagnosticFree
                      exact .continueBranch beforeContinue
                        (continueStatement_success_sound primary)
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
                      exact .fallbackBranch beforeFallback
                        (assignmentOrExpressionStatement_success_sound
                          expression expressionParses expressionReflects
                            expressionSound diagnosticFree result)

end Solcore.Syntax.Parser.TermInternals
