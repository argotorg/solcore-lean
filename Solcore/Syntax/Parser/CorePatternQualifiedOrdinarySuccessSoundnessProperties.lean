import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeGrammar
import Solcore.Syntax.Parser.CorePatternArgumentsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternQualifiedNameOrdinaryOutcomeSoundnessProperties

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
