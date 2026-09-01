import Solcore.Syntax.DeclarativeYulExpressionGrammar
import Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-!
Diagnostic reflection and exact ordered soundness for transactional inline-Yul
call arguments.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulLeftParenTokenAtOfIsSymbol
    {input : State} (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol .leftParen) = true at present
      have parsed : symbol .leftParen .yulExpression input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span,
        (symbol_ok_tokenAt .leftParen .yulExpression parsed).1⟩

/-- Optional Yul call arguments reflect diagnostics through either successful
transactional branch. -/
theorem optionalYulCallArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalYulCallArguments nested) := by
  intro input arguments next result diagnosticFree
  unfold optionalYulCallArguments at result
  split at result
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      (Parser.bind_reflectsDiagnosticFreeOnSuccess
        (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
          nested .yulExpression .yul nestedReflects)
        (fun values => Parser.pure_reflectsDiagnosticFreeOnSuccess
          (some values)))
      (Parser.pure_reflectsDiagnosticFreeOnSuccess none)
      input arguments next result diagnosticFree
  · cases result
    exact diagnosticFree

/-- Every diagnostic-free optional-call success records absence, a disjoint
ordinary-rejection fallback, or the exact preferred argument-list grammar. -/
theorem optionalYulCallArguments_success_sound
    (nested : Parser YulExpr)
    (nestedParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback : DeclarativeGrammar.YulCallArgumentsFallbackSpec nestedParses)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (rejectSound : ∀ {input failed : State} {failure : Failure},
      delimited .leftParen .rightParen true nested .yulExpression .yul input =
          .reject failure failed →
        fallback.rejects input.declarativeRemainder)
    {input next : State}
    {arguments : Option (DelimitedList YulExpr)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalYulCallArguments nested input = .ok arguments next) :
    DeclarativeGrammar.OptionalYulCallArgumentsParses nestedParses fallback
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold optionalYulCallArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : delimited .leftParen .rightParen true nested
        .yulExpression .yul input with
    | invariant error =>
        simp [bind, argumentsResult] at result
    | reject failure failed =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases yulLeftParenTokenAtOfIsSymbol present with
          ⟨openingSpan, openingToken⟩
        exact .rewound openingSpan openingToken
          (rejectSound argumentsResult)
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present
          (delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
            .leftParen .rightParen nested nestedParses .yulExpression .yul
            nestedSound nestedReflects nestedShape diagnosticFree
            argumentsResult)
  · have absentBool : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absentBool, Bool.false_eq_true, if_false] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absentBool)

end Solcore.Syntax.Parser
