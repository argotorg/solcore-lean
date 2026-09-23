import Solcore.Syntax.DeclarativeCoreExpressionPostfixGrammar
import Solcore.Syntax.Parser.CoreExpressionPostfixDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Exact parser-independent soundness for maximal Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every diagnostic-free postfix-tail success follows the exact maximal
index/call/field grammar, including branch priority and stopping evidence. -/
theorem postfixTail_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    ∀ fuel base input expression next,
      next.diagnosticsRev = [] →
      postfixTail nested block fuel base input = .ok expression next →
      DeclarativeGrammar.PostfixTailParses nestedParses
        input.declarativeRemainder base expression
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression next diagnosticFree result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression next diagnosticFree result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have afterClosingFree :=
                      postfixTail_reflectsDiagnosticFreeOnSuccess nested block
                        nestedReflects fuel {
                          span := SourceSpan.cover base.span closing.span
                          value := .index base
                            (SourceSpan.cover opening.span closing.span) index
                        } afterClosing expression next result diagnosticFree
                    have afterIndexFree :=
                      symbol_reflectsDiagnosticFreeOnSuccess .rightBracket
                        .expression afterIndex closing afterClosing
                          closingResult afterClosingFree
                    exact .index opening.span closing.span
                      (symbol_success_exactTokenParses .leftBracket
                        .expression openingResult)
                      (nestedSound afterIndexFree indexResult)
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing expression next diagnosticFree result)
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        have indexedFalse : isSymbol input .leftBracket = false := by
          simp_all
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have afterArgumentsFree :=
                postfixTail_reflectsDiagnosticFreeOnSuccess nested block
                  nestedReflects fuel {
                    span := SourceSpan.cover base.span arguments.span
                    value := .call base arguments
                  } afterArguments expression next result diagnosticFree
              exact .call indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
                  .leftParen .rightParen nested nestedParses .expression
                    .expression nestedSound nestedReflects nestedShape
                      afterArgumentsFree argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments expression next diagnosticFree result)
        · simp only [called, Bool.false_eq_true, if_false] at result
          have calledFalse : isSymbol input .leftParen = false := by
            simp_all
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false
            .leftParen calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .field dot.span indexAbsent callAbsent
                      (symbol_success_exactTokenParses .dot .expression
                        dotResult)
                      (identifier_success_sound .expression nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName expression next diagnosticFree result)
          · simp only [field] at result
            cases result
            have fieldFalse : isSymbol input .dot = false := by
              simp_all
            exact .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot fieldFalse⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free complete postfix success consists of one supplied
atom followed by its exact maximal postfix suffix sequence. -/
theorem expressionPostfix_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomParses nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
      expressionAtom nested block input = .ok value next →
      atomParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionPostfix nested block input = .ok expression next) :
    DeclarativeGrammar.ExpressionPostfixParses atomParses nestedParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      have afterAtomFree :=
        ExpressionAtomInternals.postfixTail_reflectsDiagnosticFreeOnSuccess
          nested block nestedReflects (afterAtom.remainingCount + 1) base
            afterAtom expression next result diagnosticFree
      exact ⟨base, afterAtom.declarativeRemainder,
        atomSound afterAtomFree atomResult,
        ExpressionAtomInternals.postfixTail_success_sound nested block
          nestedParses nestedReflects nestedSound nestedShape
            (afterAtom.remainingCount + 1) base afterAtom expression next
              diagnosticFree result⟩

end Solcore.Syntax.Parser
