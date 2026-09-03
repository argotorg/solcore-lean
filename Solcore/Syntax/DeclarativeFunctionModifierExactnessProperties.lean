import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Shared exact values for optional hard-keyword function modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem modifier_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- One optional function modifier fixes its absent or present span. -/
theorem OptionalFunctionModifierParses.value_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim
            (modifier_absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (modifier_absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken =>
          rw [leftToken.span_unique rightToken]

/-- One optional function modifier fixes its value and final remainder. -/
theorem OptionalFunctionModifierParses.result_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
