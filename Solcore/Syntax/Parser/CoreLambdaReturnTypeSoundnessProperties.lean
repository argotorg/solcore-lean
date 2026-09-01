import Solcore.Syntax.Parser.CoreLambdaParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-!
Exact declarative soundness for optional Core lambda return types.
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

/-- Every successful optional lambda return type retains exact arrow absence or
the exact arrow and recursive type transition. -/
theorem optionalLambdaReturnType_success_sound {input next : State}
    {value : Option TypeExpr}
    (result : optionalLambdaReturnType input = .ok value next) :
    DeclarativeGrammar.OptionalLambdaReturnTypeParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨arrow, afterArrow, arrowResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    cases finished
    exact .present arrow.span
      (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
      (typeExpr_success_sound typeResult)
  · have arrowAbsent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [arrowAbsent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .arrow arrowAbsent)

end Solcore.Syntax.Parser.ExpressionAtomInternals
