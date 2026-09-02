import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact values for fixed-order public/payable contract-entry modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem modifier_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- One optional hard-keyword modifier has one exact optional span. -/
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
          have spanEq := leftToken.span_unique rightToken
          cases spanEq
          rfl

/-- One optional modifier fixes its optional span and final remainder. -/
theorem OptionalFunctionModifierParses.result_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Fixed public-then-payable modifiers have one exact payable marker value. -/
theorem ContractEntryModifiersOrdinaryParses.value_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftPublic leftPayable =>
      cases rightParsed with
      | parsed rightPublic rightPayable =>
          have afterPublicEq := leftPublic.output_unique rightPublic
          cases afterPublicEq
          exact leftPayable.value_unique rightPayable

/-- Fixed public-then-payable modifiers fix their value and remainder. -/
theorem ContractEntryModifiersOrdinaryParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
