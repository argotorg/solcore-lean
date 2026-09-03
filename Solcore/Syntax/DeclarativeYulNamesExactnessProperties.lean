import Solcore.Syntax.DeclarativeYulExpressionLeafExactnessProperties

/-! Exact source-order names and spans of ordinary Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed accumulated name tail fixes the finished span and forward names. -/
theorem YulNamesTailOrdinaryParses.value_unique
    {first : Syntax.YulIdentifier} {input : Remainder}
    {last : Syntax.YulIdentifier} {tailRev : List Syntax.YulIdentifier}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesTailOrdinaryParses first input last tailRev left afterLeft)
    (rightParsed : YulNamesTailOrdinaryParses first input last tailRev right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent leftFinished =>
      cases rightParsed with
      | done _ rightFinished => cases leftFinished; cases rightFinished; rfl
      | next rightSpan rightToken _ _ => exact False.elim (leftAbsent ⟨_, rightToken⟩)
  | next leftSpan leftToken leftName leftTail ih =>
      cases rightParsed with
      | done rightAbsent _ => exact False.elim (rightAbsent ⟨_, leftToken⟩)
      | next _ _ rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          exact ih rightTail

/-- An ordinary Yul name sequence fixes its span and forward-order names. -/
theorem YulNamesOrdinaryParses.value_unique {input : Remainder}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesOrdinaryParses input left afterLeft)
    (rightParsed : YulNamesOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          exact leftTail.value_unique rightTail

/-- An ordinary name sequence fixes its complete successful result. -/
theorem YulNamesOrdinaryParses.result_unique {input : Remainder}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesOrdinaryParses input left afterLeft)
    (rightParsed : YulNamesOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
