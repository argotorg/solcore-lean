import Solcore.Syntax.DeclarativeCorePatternConstructorGrammar
import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingNonemptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.PatternProperties

/-!
Diagnostic reflection and exact token soundness for constructor-pattern names
and their transactional argument lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bindOkComponents {alpha beta : Type} {first : Parser alpha}
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

private theorem leftParenTokenAtOfIsSymbol
    {input : State} (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol .leftParen) = true at present
      have parsed : symbol .leftParen .pattern input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, (symbol_ok_tokenAt .leftParen .pattern parsed).1⟩

/-- Pattern-name success reflects through the Boolean-first branch. -/
theorem patternName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess patternName := by
  intro input name next result diagnosticFree
  unfold patternName at result
  split at result
  · exact booleanIdentifier_reflectsDiagnosticFreeOnSuccess input name next
      result diagnosticFree
  · exact identifier_reflectsDiagnosticFreeOnSuccess .pattern input name
      next result diagnosticFree

/-- Nonempty refinement is non-consuming and cannot erase diagnostics. -/
theorem requirePatternArguments_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requirePatternArguments values) := by
  intro input arguments next result diagnosticFree
  unfold requirePatternArguments at result
  cases elements : values.elements with
  | nil => simp [elements] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact diagnosticFree

/-- Required argument parsing reflects through delimiters and nested values. -/
theorem constructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (constructorArguments nested) := by
  unfold constructorArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess .leftParen
      .rightParen false nested .pattern .pattern nestedReflects)
  exact requirePatternArguments_reflectsDiagnosticFreeOnSuccess

/-- Transactional optional arguments reflect through either successful path. -/
theorem optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalConstructorArguments nested) := by
  intro input arguments next result diagnosticFree
  unfold optionalConstructorArguments at result
  split at result
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      (Parser.bind_reflectsDiagnosticFreeOnSuccess
        (constructorArguments_reflectsDiagnosticFreeOnSuccess nested
          nestedReflects)
        (fun values => Parser.pure_reflectsDiagnosticFreeOnSuccess
          (some values)))
      (Parser.pure_reflectsDiagnosticFreeOnSuccess none)
      input arguments next result diagnosticFree
  · cases result
    exact diagnosticFree

/-- Diagnostic-free checked identifiers exclude the parser's hyphen error. -/
theorem identifier_hyphenAbsent_of_diagnosticFree (context : ParseContext)
    {input next : State} {name : Identifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : identifier context input = .ok name next) :
    name.value.toList.contains '-' = false := by
  unfold identifier at result
  cases rawResult : rawIdentifier context input with
  | invariant error => simp [rawResult] at result
  | reject failure rejected => simp [rawResult] at result
  | ok parsedName afterName =>
      simp only [rawResult] at result
      split at result
      · cases result
        simp [State.emit] at diagnosticFree
      · cases result
        exact Bool.eq_false_iff.mpr (by assumption)

/--
Every diagnostic-free name retains exact Boolean-first priority and excludes
the checked ordinary-identifier hyphen diagnostic.
-/
theorem patternName_success_sound {input next : State} {name : Identifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternName input = .ok name next) :
    DeclarativeGrammar.PatternNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold patternName at result
  split at result
  · exact .boolean (booleanIdentifier_success_sound result)
  · have booleanAbsent : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr (by assumption)
    have absences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using booleanAbsent)
    exact .identifier
      (keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1)
      (keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2)
      (identifier_hyphenAbsent_of_diagnosticFree .pattern diagnosticFree
        result)
      (identifier_success_sound .pattern result)

/-- Successful refinement fixes the nonempty carrier and changes no state. -/
theorem requirePatternArguments_success_sound
    {values : DelimitedList Pattern} {input next : State}
    {arguments : NonemptyDelimitedList Pattern}
    (result : requirePatternArguments values input = .ok arguments next) :
    DeclarativeGrammar.RequirePatternArgumentsParses values
      input.declarativeRemainder arguments next.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requirePatternArguments at result
  cases elements with
  | nil => simp at result
  | cons head tail =>
      simp only [pure] at result
      cases result
      exact .parsed

/-- Diagnostic-free required arguments have exact nonempty no-trailing syntax. -/
theorem constructorArguments_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {arguments : NonemptyDelimitedList Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorArguments nested input = .ok arguments next) :
    DeclarativeGrammar.ConstructorArgumentsParses nestedParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold constructorArguments at result
  rcases bindOkComponents result with
    ⟨values, afterValues, valuesResult, requiredResult⟩
  rcases values with ⟨span, elements⟩
  have afterValuesFree :=
    requirePatternArguments_reflectsDiagnosticFreeOnSuccess
      { span := span, elements := elements }
      afterValues arguments next requiredResult diagnosticFree
  have valuesGrammar :=
    delimitedNoTrailing_nonempty_success_sound_of_diagnosticFree
      .leftParen .rightParen nested nestedParses .pattern .pattern
      nestedSound nestedReflects nestedShape afterValuesFree valuesResult
  unfold requirePatternArguments at requiredResult
  cases elements with
  | nil => simp at requiredResult
  | cons head tail =>
      simp only [pure] at requiredResult
      cases requiredResult
      simpa only [DeclarativeGrammar.ConstructorArgumentsParses,
        NonemptyList.toList] using valuesGrammar

/--
Optional arguments distinguish absence, successful presence, and an exact
rewind after a leading-parenthesis attempt rejected.
-/
theorem optionalConstructorArguments_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State}
    {arguments : Option (NonemptyDelimitedList Pattern)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalConstructorArguments nested input =
      .ok arguments next) :
    DeclarativeGrammar.OptionalConstructorArgumentsParses nestedParses
      fallback input.declarativeRemainder arguments
        next.declarativeRemainder := by
  unfold optionalConstructorArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : constructorArguments nested input with
    | invariant error => simp [bind, argumentsResult] at result
    | reject failure rejected =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases leftParenTokenAtOfIsSymbol present with
          ⟨openingSpan, openingToken⟩
        exact .rewound openingSpan openingToken
          (argumentsRejectionSound argumentsResult)
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present (constructorArguments_success_sound nested nestedParses
          nestedReflects nestedSound nestedShape diagnosticFree argumentsResult)
  · have absentBool : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absentBool, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absentBool)

end Solcore.Syntax.Parser.PatternInternals
