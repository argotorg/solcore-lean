import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionModifierExactnessProperties

/-! Exact values for fixed-order public/payable contract-entry modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

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
