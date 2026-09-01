import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.Pattern

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
