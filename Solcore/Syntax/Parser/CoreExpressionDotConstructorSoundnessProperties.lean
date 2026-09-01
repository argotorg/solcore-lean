import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptyDiagnosticFreeSoundnessProperties

/-!
Diagnostic reflection and exact declarative soundness for leading-dot Core
expression constructors.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Optional leading-dot arguments reflect through every nested element. -/
theorem optionalDotConstructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalDotConstructorArguments nested) := by
  unfold optionalDotConstructorArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
        .leftParen .rightParen true nested .expression .expression
          nestedReflects)
    intro arguments
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Leading-dot construction reflects through its name and arguments. -/
theorem dotConstructor_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (dotConstructor nested) := by
  unfold dotConstructor
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .dot .expression)
  intro dot
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    expressionName_reflectsDiagnosticFreeOnSuccess
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalDotConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/--
Diagnostic-free optional arguments preserve opening-token priority and the
exact no-trailing delimited grammar.
-/
theorem optionalDotConstructorArguments_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {arguments : Option (DelimitedList Expr)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalDotConstructorArguments nested input =
      .ok arguments next) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsParses nestedParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true
        nested .expression .expression input with
    | invariant error => simp [argumentsResult] at result
    | reject failure rejected => simp [argumentsResult] at result
    | ok values afterArguments =>
        simp only [argumentsResult, pure] at result
        cases result
        exact .present
          (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
            .leftParen .rightParen nested nestedParses .expression .expression
            nestedSound nestedReflects nestedShape diagnosticFree
            argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/--
Every diagnostic-free leading-dot constructor success retains its exact dot,
Boolean-first name, optional arguments, span, AST, and final remainder.
-/
theorem dotConstructor_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : dotConstructor nested input = .ok expression next) :
    DeclarativeGrammar.DotConstructorParses nestedParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold dotConstructor at result
  rcases bind_ok_components result with
    ⟨dot, afterDot, dotResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  have argumentsGrammar := optionalDotConstructorArguments_success_sound
    nested nestedParses nestedReflects nestedSound nestedShape diagnosticFree
      argumentsResult
  exact .parsed dot.span
    (symbol_success_exactTokenParses .dot .expression dotResult)
    (expressionName_success_sound nameResult) argumentsGrammar

end Solcore.Syntax.Parser.ExpressionAtomInternals
