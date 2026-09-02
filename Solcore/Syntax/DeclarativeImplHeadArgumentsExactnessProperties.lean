import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeProperties

/-! Exact outcomes for required implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implHeadArgumentListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses .less .greater
        TypeExprOrdinaryParses)
      (DelimitedListRejects .less .greater false true
        TypeExprOrdinaryParses TypeExprRejects) :=
  nonemptyTrailingDelimitedListExactOutcomeSpec .less .greater
    typeExprExactOutcomeSpec

/-- Implementation head arguments fix their nonempty delimited-list AST. -/
theorem ImplHeadArgumentsOrdinaryParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    left = right := by
  have encodedEq := implHeadArgumentListExactOutcomeSpec
    |>.successValueUnique leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp [Syntax.NonemptyList.toList] at encodedEq
                  simp_all

/-- Implementation head arguments fix their AST and final remainder. -/
theorem ImplHeadArgumentsOrdinaryParses.result_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplHeadArgumentsOrdinaryParses input left afterLeft)
    (rightParsed : ImplHeadArgumentsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Implementation head-argument rejection has one exact endpoint. -/
theorem ImplHeadArgumentsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : ImplHeadArgumentsRejects input left)
    (rightRejected : ImplHeadArgumentsRejects input right) : left = right :=
  implHeadArgumentListExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

/-- Required implementation head arguments have fully exact outcomes. -/
theorem implHeadArgumentsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplHeadArgumentsOrdinaryParses
      ImplHeadArgumentsRejects where
  toDeterministicOutcomeSpec := implHeadArgumentsDeterministicOutcomeSpec
  successValueUnique := ImplHeadArgumentsOrdinaryParses.value_unique
  rejectOutputUnique := ImplHeadArgumentsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
