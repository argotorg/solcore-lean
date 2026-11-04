import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Internal.PatternOutcomes
import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Parser.Internal.PatternSoundness

/-!
Soundness of the parsers of one pattern step: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedFallbackRejectionSoundnessProperties
/-!
Concrete rejection reflection for transactional pattern and Yul argument
fallbacks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace PatternInternals

/-- Required constructor arguments add no ordinary rejection after delimiters. -/
theorem constructorArguments_reject_sound
    (nested : Parser Pattern)
    (ordinaryParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : Pattern},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : constructorArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.DelimitedListRejects .leftParen .rightParen false false
      ordinaryParses nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold constructorArguments at result
  cases argumentsResult : delimitedNoTrailing .leftParen .rightParen false
      nested .pattern .pattern input with
  | invariant error => simp [bind, argumentsResult] at result
  | reject argumentsFailure argumentsFailed =>
      simp only [bind, argumentsResult] at result
      cases result
      exact delimitedNoTrailing_reject_sound .leftParen .rightParen false
        nested ordinaryParses nestedRejects .pattern .pattern
          nestedSuccessSound nestedRejectSound argumentsResult
  | ok values afterValues =>
      simp only [bind, argumentsResult] at result
      unfold requirePatternArguments at result
      cases elementsEq : values.elements with
      | nil => simp [elementsEq] at result
      | cons head tail => simp [elementsEq, pure] at result

/-- Existing optional-pattern consumers receive the concrete fallback proof. -/
theorem constructorArguments_fallback_reject_sound
    (nested : Parser Pattern)
    (ordinaryParses cleanParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec ordinaryParses
      nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    (nestedSuccessSound : ∀ {input next : State} {value : Pattern},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : constructorArguments nested input =
      .reject failure rejected) :
    (DeclarativeGrammar.ConstructorArgumentsFallbackSpec.ofOutcomes
      ordinaryParses cleanParses nestedRejects outcomes
        cleanToOrdinary).rejects input.declarativeRemainder := by
  exact ⟨rejected.declarativeRemainder,
    constructorArguments_reject_sound nested ordinaryParses nestedRejects
      nestedSuccessSound nestedRejectSound result⟩

end PatternInternals

/-- Exact rejection reflection for allow-empty/trailing Yul call arguments. -/
theorem yulCallArguments_reject_sound
    (nested : Parser YulExpr)
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimited .leftParen .rightParen true nested .yulExpression
      .yul input = .reject failure rejected) :
    DeclarativeGrammar.DelimitedListRejects .leftParen .rightParen true true
      ordinaryParses nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  delimited_reject_sound .leftParen .rightParen true nested ordinaryParses
    nestedRejects .yulExpression .yul nestedSuccessSound nestedRejectSound
      result

/-- Existing optional-Yul consumers receive the concrete fallback proof. -/
theorem yulCallArguments_fallback_reject_sound
    (nested : Parser YulExpr)
    (ordinaryParses cleanParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec ordinaryParses
      nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimited .leftParen .rightParen true nested .yulExpression
      .yul input = .reject failure rejected) :
    (DeclarativeGrammar.YulCallArgumentsFallbackSpec.ofOutcomes ordinaryParses
      cleanParses nestedRejects outcomes cleanToOrdinary).rejects
        input.declarativeRemainder := by
  exact ⟨rejected.declarativeRemainder,
    yulCallArguments_reject_sound nested ordinaryParses nestedRejects
      nestedSuccessSound nestedRejectSound result⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternArgumentsOrdinaryOutcomeSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternQualifiedOrdinarySuccessSoundnessProperties
/-! Executable ordinary-success reflection for `qualifiedPattern`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable qualified-pattern success retains its maximal path,
transactional optional arguments, exact binder choice, AST span, and output. -/
theorem qualifiedPattern_success_ordinary_sound
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
    {input output : State} {pattern : Pattern}
    (result : qualifiedPattern nested input = .ok pattern output) :
    DeclarativeGrammar.QualifiedPatternOrdinaryParses nestedOrdinary
      nestedRejects input.declarativeRemainder pattern
        output.declarativeRemainder := by
  unfold qualifiedPattern at result
  rcases bind_ok_components result with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases componentsEq : path.value.components.toList.reverse with
  | nil => simp [componentsEq] at finished
  | cons name qualifiersRev =>
      simp only [componentsEq] at finished
      split at finished
      · rename_i binderChoice
        change DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
          arguments name = true at binderChoice
        cases finished
        have pathParsed := patternQualifiedName_success_ordinary_sound
          pathResult
        have argumentsParsed :=
          optionalConstructorArguments_success_ordinary_sound nested
            nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
              nestedShape argumentsResult
        have qualifiersEmpty : qualifiersRev = [] := by
          have parts : (qualifiersRev = [] ∧ arguments = none) ∧
              DeclarativeGrammar.patternIdentifierStartsWithLowercase name =
                true := by
            simpa [DeclarativeGrammar.qualifiedPatternIsBinder] using
              binderChoice
          exact parts.1.1
        subst qualifiersRev
        exact .binder pathParsed argumentsParsed componentsEq binderChoice
      · rename_i constructorChoice
        change DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
          arguments name ≠ true at constructorChoice
        have constructorChoiceBool :
            DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
              arguments name = false :=
          Bool.eq_false_iff.mpr constructorChoice
        cases finished
        exact .constructor
          (patternQualifiedName_success_ordinary_sound pathResult)
          (optionalConstructorArguments_success_ordinary_sound nested
            nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
              nestedShape argumentsResult)
          componentsEq constructorChoiceBool

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternQualifiedOrdinaryRejectionSoundnessProperties
/-! Executable ordinary-rejection reflection for `qualifiedPattern`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable qualified-pattern rejection follows the exact maximal
path rejection; the optional-arguments rejection case is retained
compositionally even though that transactional parser cannot reject. -/
theorem qualifiedPattern_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input rejected : State} {failure : Failure}
    (result : qualifiedPattern nested input = .reject failure rejected) :
    DeclarativeGrammar.QualifiedPatternRejects nestedOrdinary nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold qualifiedPattern at result
  simp only [bind] at result
  cases pathResult : qualifiedName .pattern .pattern input with
  | invariant error => simp [pathResult] at result
  | reject pathFailure pathRejected =>
      simp only [pathResult] at result
      cases result
      exact .pathRejected
        (patternQualifiedName_reject_ordinary_sound pathResult)
  | ok path afterPath =>
      simp only [pathResult] at result
      cases argumentsResult : optionalConstructorArguments nested afterPath with
      | invariant error => simp [argumentsResult] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected
            (patternQualifiedName_success_ordinary_sound pathResult)
            (optionalConstructorArguments_reject_ordinary_sound nested
              argumentsResult)
      | ok arguments afterArguments =>
          simp only [argumentsResult] at result
          cases componentsEq : path.value.components.toList.reverse with
          | nil => simp [componentsEq] at result
          | cons name qualifiersRev =>
              simp only [componentsEq] at result
              split at result <;> simp [pure] at result

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternQualifiedOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for `qualifiedPattern`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package exact success and rejection over supplied nested-pattern outcome
bridges. -/
theorem qualifiedPattern_ordinaryOutcome_sound
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
    (∀ {input output : State} {pattern : Pattern},
      qualifiedPattern nested input = .ok pattern output →
        DeclarativeGrammar.QualifiedPatternOrdinaryParses nestedOrdinary
          nestedRejects input.declarativeRemainder pattern
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      qualifiedPattern nested input = .reject failure rejected →
        DeclarativeGrammar.QualifiedPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨qualifiedPattern_success_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound nestedShape,
    qualifiedPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects⟩

/-- Re-export deterministic qualified-pattern outcomes. -/
theorem qualifiedPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.QualifiedPatternOrdinaryParses nestedOrdinary
        nestedRejects)
      (DeclarativeGrammar.QualifiedPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.qualifiedPatternDeterministicOutcomeSpec nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternDotConstructorOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for leading-dot Core constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable success retains its exact dot, diagnostic-inclusive
Boolean-first name, transactional optional arguments, AST, span, and final
remainder. -/
theorem dotConstructorPattern_success_ordinary_sound
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
    {input output : State} {pattern : Pattern}
    (result : dotConstructorPattern nested input = .ok pattern output) :
    DeclarativeGrammar.DotConstructorPatternOrdinaryParses nestedOrdinary
      nestedRejects input.declarativeRemainder pattern
        output.declarativeRemainder := by
  unfold dotConstructorPattern at result
  cases dotResult : symbol .dot .pattern input with
  | invariant error => simp [bind, dotResult] at result
  | reject failure rejected => simp [bind, dotResult] at result
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : patternName afterDot with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult, pure] at result
              cases result
              exact .parsed dot.span
                (symbol_success_exactTokenParses .dot .pattern dotResult)
                (patternName_success_ordinary_sound nameResult)
                (optionalConstructorArguments_success_ordinary_sound nested
                  nestedOrdinary nestedRejects nestedSuccessSound
                    nestedRejectSound nestedShape argumentsResult)

/-- Every executable rejection records the first failing sequential stage.
In particular, a missing dot is non-consuming, while a rejected name follows
the exact consumed dot. -/
theorem dotConstructorPattern_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input rejected : State} {failure : Failure}
    (result : dotConstructorPattern nested input = .reject failure rejected) :
    DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold dotConstructorPattern at result
  cases dotResult : symbol .dot .pattern input with
  | invariant error => simp [bind, dotResult] at result
  | reject dotFailure afterDot =>
      simp only [bind, dotResult] at result
      have rejectedEq : afterDot = rejected := by injection result
      subst rejected
      have stateEq := symbol_reject_state_eq .dot .pattern dotResult
      rw [stateEq]
      exact .dotMissing
        (symbol_reject_tokenKindAbsentAt .dot .pattern dotResult)
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : patternName afterDot with
      | invariant error => simp [nameResult] at result
      | reject nameFailure afterName =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected dot.span
            (symbol_success_exactTokenParses .dot .pattern dotResult)
            (patternName_reject_ordinary_sound nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp [argumentsResult, pure] at result
          | reject argumentsFailure afterArguments =>
              simp only [argumentsResult] at result
              cases result
              exact .argumentsRejected dot.span
                (symbol_success_exactTokenParses .dot .pattern dotResult)
                (patternName_success_ordinary_sound nameResult)
                (optionalConstructorArguments_reject_ordinary_sound nested
                  argumentsResult)

/-- Package both executable leading-dot constructor-pattern outcomes. -/
theorem dotConstructorPattern_ordinaryOutcome_sound
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
    (∀ {input output : State} {pattern : Pattern},
      dotConstructorPattern nested input = .ok pattern output →
        DeclarativeGrammar.DotConstructorPatternOrdinaryParses
          nestedOrdinary nestedRejects input.declarativeRemainder pattern
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      dotConstructorPattern nested input = .reject failure rejected →
        DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨dotConstructorPattern_success_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound nestedShape,
    dotConstructorPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects⟩

/-- Lift deterministic nested outcomes through the executable leading-dot
constructor-pattern relation. -/
theorem dotConstructorPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.DotConstructorPatternOrdinaryParses nestedOrdinary
        nestedRejects)
      (DeclarativeGrammar.DotConstructorPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.dotConstructorPatternDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternStepOrdinaryOutcomeSoundnessProperties
/-! One-call executable outcomes for a complete Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Compose the four recursive branches, ordered core dispatcher, and public
recovery boundary into one executable ordinary outcome. -/
theorem corePatternStep_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (relations : DeclarativeGrammar.CorePatternStepRelations)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → relations.nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → relations.nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (expressionSuccessSound :
      ∀ {input output : State} {value : Expr},
        expression input = .ok value output → relations.expressionOrdinary
          input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        expression input = .reject failure rejected →
          relations.expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    (∀ {input output : State} {pattern : Pattern},
      patternLayer nested expression input = .ok pattern output →
        DeclarativeGrammar.CorePatternStepOrdinaryParses relations
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternLayer nested expression input = .reject failure rejected →
        DeclarativeGrammar.CorePatternStepRejects relations
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have parenthesizedSound :=
    PatternInternals.parenthesizedPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound
  have dotSound :=
    PatternInternals.dotConstructorPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound nestedWindow
  have comptimeSound :=
    PatternInternals.comptimePattern_ordinaryOutcome_sound expression
      relations.expressionOrdinary relations.expressionRejects
        expressionSuccessSound expressionRejectSound
  have qualifiedSound :=
    PatternInternals.qualifiedPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound nestedWindow
  have coreSound := PatternInternals.patternCore_ordinaryOutcome_sound nested
    expression relations.parenthesizedOrdinary
      relations.dotConstructorOrdinary relations.comptimeOrdinary
        relations.qualifiedOrdinary relations.parenthesizedRejects
          relations.dotConstructorRejects relations.comptimeRejects
            relations.qualifiedRejects parenthesizedSound.1 dotSound.1
              comptimeSound.1 qualifiedSound.1 parenthesizedSound.2
                dotSound.2 comptimeSound.2 qualifiedSound.2
  have coreWindow := PatternInternals.patternCore_preservesTokenWindow nested
    expression nestedWindow expressionWindow
  exact patternLayer_ordinaryOutcome_sound nested expression
    relations.coreOrdinary relations.coreRejects coreSound.1 coreSound.2
      coreWindow

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem corePatternStep_ordinaryOutcomeSpec
    (relations : DeclarativeGrammar.CorePatternStepRelations)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CorePatternStepOrdinaryParses relations)
      (DeclarativeGrammar.CorePatternStepRejects relations) :=
  DeclarativeGrammar.corePatternStepDeterministicOutcomeSpec relations
    nestedOutcomes expressionOutcomes

end Solcore.Syntax.Parser
end
