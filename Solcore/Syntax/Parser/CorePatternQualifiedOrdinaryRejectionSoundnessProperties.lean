import Solcore.Syntax.Parser.CorePatternQualifiedOrdinarySuccessSoundnessProperties

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
