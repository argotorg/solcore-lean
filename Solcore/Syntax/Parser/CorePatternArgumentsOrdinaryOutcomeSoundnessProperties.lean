import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeProperties
import Solcore.Syntax.Parser.DelimitedFallbackRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties
import Solcore.Syntax.Parser.Pattern

/-! Executable ordinary outcomes for Core constructor-pattern arguments. -/

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

/-- Every required constructor-argument success has the exact nonempty,
no-trailing declarative shape. -/
theorem constructorArguments_success_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State}
    {arguments : NonemptyDelimitedList Pattern}
    (result : constructorArguments nested input = .ok arguments output) :
    DeclarativeGrammar.ConstructorArgumentsOrdinaryParses nestedOrdinary
      input.declarativeRemainder arguments output.declarativeRemainder := by
  unfold constructorArguments at result
  rcases bindOkComponents result with
    ⟨values, afterValues, valuesResult, requiredResult⟩
  rcases values with ⟨span, elements⟩
  have valuesParsed :=
    delimitedNoTrailing_nonempty_success_sound .leftParen .rightParen nested
      nestedOrdinary .pattern .pattern nestedSuccessSound nestedShape
        valuesResult
  unfold requirePatternArguments at requiredResult
  cases elements with
  | nil => simp at requiredResult
  | cons head tail =>
      simp only [pure] at requiredResult
      cases requiredResult
      simpa only [DeclarativeGrammar.ConstructorArgumentsOrdinaryParses,
        DeclarativeGrammar.ConstructorArgumentsParses,
        NonemptyList.toList] using valuesParsed

/-- Every required constructor-argument rejection records the exact
nonempty, no-trailing rejection trace. -/
theorem constructorArguments_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : constructorArguments nested input = .reject failure rejected) :
    DeclarativeGrammar.ConstructorArgumentsOrdinaryRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  exact constructorArguments_reject_sound nested nestedOrdinary nestedRejects
    nestedSuccessSound nestedRejectSound result

/-- Package both required constructor-argument executable outcomes. -/
theorem constructorArguments_ordinaryOutcome_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State}
      {arguments : NonemptyDelimitedList Pattern},
      constructorArguments nested input = .ok arguments output →
        DeclarativeGrammar.ConstructorArgumentsOrdinaryParses nestedOrdinary
          input.declarativeRemainder arguments output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        DeclarativeGrammar.ConstructorArgumentsOrdinaryRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨constructorArguments_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound nestedShape,
    constructorArguments_reject_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound⟩

/-- Lift deterministic nested outcomes through required arguments. -/
theorem constructorArguments_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ConstructorArgumentsOrdinaryParses nestedOrdinary)
      (DeclarativeGrammar.ConstructorArgumentsOrdinaryRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.constructorArgumentsDeterministicOutcomeSpec
    nestedOutcomes

/-- Every optional constructor-argument success is exact absence, exact
transactional rewind after rejection, or committed required arguments. -/
theorem optionalConstructorArguments_success_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State}
    {arguments : Option (NonemptyDelimitedList Pattern)}
    (result : optionalConstructorArguments nested input =
      .ok arguments output) :
    DeclarativeGrammar.OptionalConstructorArgumentsOrdinaryParses
      nestedOrdinary nestedRejects input.declarativeRemainder arguments
        output.declarativeRemainder := by
  unfold optionalConstructorArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : constructorArguments nested input with
    | invariant error => simp [bind, argumentsResult] at result
    | reject failure rejected =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .pattern present
            with ⟨opening, openingResult⟩
        exact .rewound opening.span
          (symbol_ok_tokenAt .leftParen .pattern openingResult).1
          ⟨rejected.declarativeRemainder,
            constructorArguments_reject_ordinary_sound nested
              nestedOrdinary nestedRejects nestedSuccessSound
                nestedRejectSound argumentsResult⟩
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present
          (constructorArguments_success_ordinary_sound nested
            nestedOrdinary nestedSuccessSound nestedShape argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/-- The transactional optional parser has no executable rejection. -/
theorem optionalConstructorArguments_reject_ordinary_sound
    (nested : Parser Pattern)
    {input rejected : State} {failure : Failure}
    (result : optionalConstructorArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalConstructorArgumentsRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold DeclarativeGrammar.OptionalConstructorArgumentsRejects
  unfold optionalConstructorArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : constructorArguments nested input with
    | invariant error => simp [bind, argumentsResult] at result
    | reject argumentsFailure argumentsRejected =>
        simp [bind, argumentsResult, pure] at result
    | ok arguments output => simp [bind, argumentsResult, pure] at result
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent] at result

/-- Package the transactional optional executable outcome. -/
theorem optionalConstructorArguments_ordinaryOutcome_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State}
      {arguments : Option (NonemptyDelimitedList Pattern)},
      optionalConstructorArguments nested input = .ok arguments output →
        DeclarativeGrammar.OptionalConstructorArgumentsOrdinaryParses
          nestedOrdinary nestedRejects input.declarativeRemainder arguments
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalConstructorArguments nested input = .reject failure rejected →
        DeclarativeGrammar.OptionalConstructorArgumentsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨optionalConstructorArguments_success_ordinary_sound nested
      nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
        nestedShape,
    optionalConstructorArguments_reject_ordinary_sound nested⟩

/-- Lift deterministic nested outcomes through transactional optional
arguments. -/
theorem optionalConstructorArguments_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects)
      DeclarativeGrammar.OptionalConstructorArgumentsRejects :=
  DeclarativeGrammar.optionalConstructorArgumentsDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
