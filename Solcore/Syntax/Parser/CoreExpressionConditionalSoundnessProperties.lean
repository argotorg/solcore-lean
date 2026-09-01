import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-!
Diagnostic reflection and declarative soundness for the generic conditional
expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- The fuel-bounded conditional tail never removes an earlier diagnostic. -/
theorem conditionalTail_reflectsDiagnosticFreeOnSuccess
    (nested alternative : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative) :
    ∀ fuel headsRev condition,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (conditionalTail nested alternative fuel headsRev condition) := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input value next result diagnosticFree
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input value next result diagnosticFree
      unfold conditionalTail at result
      split at result
      · cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        have afterAlternativeFree := inductionHypothesis
                          ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: headsRev) nextCondition afterAlternative value
                            next result diagnosticFree
                        have afterColonFree := alternativeReflects afterColon
                          nextCondition afterAlternative alternativeResult
                            afterAlternativeFree
                        have afterThenFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .colon
                            .expression afterThen colon afterColon colonResult
                              afterColonFree
                        have afterQuestionFree := nestedReflects afterQuestion
                          thenBranch afterThen thenResult afterThenFree
                        exact symbol_reflectsDiagnosticFreeOnSuccess .question
                          .expression input question afterQuestion questionResult
                            afterQuestionFree
      · cases result
        exact diagnosticFree

/-- Public conditional parsing reflects through its first alternative. -/
theorem conditional_reflectsDiagnosticFreeOnSuccess
    (nested alternative : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (conditional nested alternative) := by
  intro input value next result diagnosticFree
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      have afterConditionFree :=
        conditionalTail_reflectsDiagnosticFreeOnSuccess nested alternative
          nestedReflects alternativeReflects
            (afterCondition.remainingCount + 1) [] condition afterCondition
              value next result diagnosticFree
      exact alternativeReflects input condition afterCondition
        alternativeResult afterConditionFree

private theorem conditionalTail_success_sound_strong
    (nested alternative : Parser Expr)
    (nestedParses alternativeParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative)
    (alternativeSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → alternative input = .ok value next →
        alternativeParses input.declarativeRemainder value
          next.declarativeRemainder) :
    ∀ fuel headsRev condition input value next,
      next.diagnosticsRev = [] →
      conditionalTail nested alternative fuel headsRev condition input =
          .ok value next →
      ∃ tailExpression,
        value = headsRev.foldl foldConditionalHead tailExpression ∧
        DeclarativeGrammar.ConditionalTailParses nestedParses
          alternativeParses input.declarativeRemainder condition tailExpression
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input value next diagnosticFree result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input value next diagnosticFree result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        let head : ConditionalHead := {
                          condition
                          question := question.span
                          thenBranch
                          colon := colon.span
                        }
                        rcases inductionHypothesis (head :: headsRev)
                            nextCondition afterAlternative value next
                              diagnosticFree result with
                          ⟨tailExpression, valueEq, tailGrammar⟩
                        have afterAlternativeFree :=
                          conditionalTail_reflectsDiagnosticFreeOnSuccess
                            nested alternative nestedReflects
                              alternativeReflects fuel (head :: headsRev)
                                nextCondition afterAlternative value next result
                                  diagnosticFree
                        have afterColonFree := alternativeReflects afterColon
                          nextCondition afterAlternative alternativeResult
                            afterAlternativeFree
                        have afterThenFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .colon
                            .expression afterThen colon afterColon colonResult
                              afterColonFree
                        have nestedGrammar := nestedSound afterThenFree
                          thenResult
                        have alternativeGrammar := alternativeSound
                          afterAlternativeFree alternativeResult
                        refine ⟨foldConditionalHead tailExpression head, ?_, ?_⟩
                        · simpa [head] using valueEq
                        · simpa [head, foldConditionalHead] using
                            (DeclarativeGrammar.ConditionalTailParses.next
                              question.span colon.span
                              (symbol_success_exactTokenParses .question
                                .expression questionResult)
                              nestedGrammar
                              (symbol_success_exactTokenParses .colon
                                .expression colonResult)
                              alternativeGrammar tailGrammar)
      next questionAbsent =>
        cases result
        refine ⟨condition, rfl, .done ?_⟩
        exact symbolAbsentAt_of_isSymbol_eq_false .question
          (Bool.eq_false_iff.mpr questionAbsent)

/-- Every diagnostic-free conditional success follows the exact right fold. -/
theorem conditional_success_sound
    (nested alternative : Parser Expr)
    (nestedParses alternativeParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative)
    (alternativeSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → alternative input = .ok value next →
        alternativeParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : conditional nested alternative input = .ok value next) :
    DeclarativeGrammar.ConditionalParses nestedParses alternativeParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      have afterConditionFree :=
        conditionalTail_reflectsDiagnosticFreeOnSuccess nested alternative
          nestedReflects alternativeReflects
            (afterCondition.remainingCount + 1) [] condition afterCondition
              value next result diagnosticFree
      have conditionGrammar := alternativeSound afterConditionFree
        alternativeResult
      rcases conditionalTail_success_sound_strong nested alternative
          nestedParses alternativeParses nestedReflects nestedSound
            alternativeReflects alternativeSound
              (afterCondition.remainingCount + 1) [] condition afterCondition
                value next diagnosticFree result with
        ⟨tailExpression, valueEq, tailGrammar⟩
      simp only [List.foldl_nil] at valueEq
      subst value
      exact ⟨condition, afterCondition.declarativeRemainder,
        conditionGrammar, tailGrammar⟩

end Solcore.Syntax.Parser.ExpressionInternals
