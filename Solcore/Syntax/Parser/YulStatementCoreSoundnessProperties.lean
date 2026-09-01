import Solcore.Syntax.DeclarativeYulStatementCoreGrammar
import Solcore.Syntax.Parser.CoreYulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.CoreYulStatementRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.YulFunctionSoundnessProperties
import Solcore.Syntax.Parser.YulStatementControlSoundnessProperties
import Solcore.Syntax.Parser.YulStatementCoreDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulStatementCoreLookaheadProperties
import Solcore.Syntax.Parser.YulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.YulSwitchSoundnessProperties

/-! Exact diagnostic-free soundness for `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every clean core-dispatch success follows its exact prioritized branch. -/
theorem yulStatementCore_success_sound
    (nested : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.YulAssignmentFallbackSpec expressionParses)
    (assignmentRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      yulAssignment input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → nested input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → yulExpression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulStatementCore nested input = .ok value next) :
    DeclarativeGrammar.YulStatementCoreParses statementParses
      expressionParses fallback input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    have primary :=
      recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
        (yulBlockStatement nested) yulExpressionStatement result diagnosticFree
    exact .block .start (yulBlockStatement_success_sound nested
      statementParses nestedReflects nestedSound diagnosticFree primary)
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard :=
      .afterBlock .start
        (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      have primary :=
        recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
          yulLetStatement yulExpressionStatement result diagnosticFree
      exact .letDecl beforeLet (yulLetStatement_success_sound expressionParses
        expressionSound diagnosticFree primary)
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard :=
        .afterLet beforeLet
          (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        have primary :=
          recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
            (yulIfStatement nested) yulExpressionStatement result
              diagnosticFree
        exact .ifThen beforeIf (yulIfStatement_success_sound nested
          statementParses expressionParses nestedReflects nestedSound
            expressionSound diagnosticFree primary)
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard :=
          .afterIf beforeIf
            (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have primary :=
            recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
              (yulForStatement nested) yulExpressionStatement result
                diagnosticFree
          exact .forLoop beforeFor (yulForStatement_success_sound nested
            statementParses expressionParses nestedReflects nestedSound
              expressionSound diagnosticFree primary)
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard :=
            .afterFor beforeFor
              (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            have primary :=
              recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                (yulSwitchStatement nested) yulExpressionStatement result
                  diagnosticFree
            exact .switch beforeSwitch (yulSwitchStatement_success_sound
              nested statementParses expressionParses nestedReflects
                nestedSound expressionSound diagnosticFree primary)
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
              have primary :=
                recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                  (yulFunctionStatement nested) yulExpressionStatement result
                    diagnosticFree
              exact .functionDef beforeFunction
                (yulFunctionStatement_success_sound nested statementParses
                  nestedReflects nestedSound diagnosticFree primary)
            · have functionFalse : isKeyword input .functionKw = false :=
                Bool.eq_false_iff.mpr functionPresent
              simp only [functionFalse, Bool.false_eq_true, if_false]
                at result
              have beforeReturn :
                  DeclarativeGrammar.YulStatementCorePrefixAbsent
                    input.declarativeRemainder .returnGuard :=
                .afterFunction beforeFunction
                  (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                    functionFalse)
              by_cases returnPresent : isKeyword input .returnKw
              · simp only [returnPresent, if_true] at result
                have primary :=
                  recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                    yulReturnBuiltin yulExpressionStatement result
                      diagnosticFree
                exact .returnBuiltin beforeReturn
                  (yulReturnBuiltin_success_sound expressionParses
                    expressionSound diagnosticFree primary)
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
                  have primary :=
                    recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                        result diagnosticFree
                  exact .leave beforeLeave
                    (yulControlToken_success_sound .leaveKw .leave primary)
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.YulStatementCorePrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterLeave beforeLeave
                      (keywordAbsentAt_of_isKeyword_eq_false .leaveKw
                        leaveFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    have primary :=
                      recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                        (yulControlToken .breakKw .break) yulExpressionStatement
                          result diagnosticFree
                    exact .break beforeBreak
                      (yulControlToken_success_sound .breakKw .break primary)
                  · have breakFalse : isKeyword input .breakKw = false :=
                      Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.YulStatementCorePrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      have primary :=
                        recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
                          (yulControlToken .continueKw .continue)
                            yulExpressionStatement result diagnosticFree
                      exact .continue beforeContinue
                        (yulControlToken_success_sound .continueKw .continue
                          primary)
                    · have continueFalse :
                          isKeyword input .continueKw = false :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeName :
                          DeclarativeGrammar.YulStatementCorePrefixAbsent
                            input.declarativeRemainder .nameGuard :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      by_cases namePresent : startsYulName input
                      · simp only [namePresent, if_true] at result
                        have nameStart :=
                          yulNameStartAt_of_startsYulName_eq_true namePresent
                        unfold orElse at result
                        cases assignmentResult : yulAssignment input with
                        | invariant error => simp [assignmentResult] at result
                        | ok assignment afterAssignment =>
                            simp only [assignmentResult] at result
                            cases result
                            exact .nameChoice beforeName (.assignment nameStart
                              (yulAssignment_success_sound expressionParses
                                expressionSound diagnosticFree
                                  assignmentResult))
                        | reject failure rejected =>
                            simp only [assignmentResult] at result
                            exact .nameChoice beforeName (.rewound nameStart
                              (assignmentRejectionSound assignmentResult)
                              (yulExpressionStatement_success_sound
                                expressionParses expressionSound diagnosticFree
                                  result))
                      · have nameFalse : startsYulName input = false :=
                          Bool.eq_false_iff.mpr namePresent
                        simp only [nameFalse, Bool.false_eq_true, if_false]
                          at result
                        have beforeFallback :
                            DeclarativeGrammar.YulStatementCorePrefixAbsent
                              input.declarativeRemainder .fallback :=
                          .afterName beforeName
                            (yulNameStartAbsentAt_of_startsYulName_eq_false
                              nameFalse)
                        exact .expressionFallback beforeFallback
                          (yulExpressionStatement_success_sound expressionParses
                            expressionSound diagnosticFree result)

end Solcore.Syntax.Parser
