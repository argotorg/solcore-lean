import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeYulBlockExactnessProperties
import Solcore.Syntax.DeclarativeYulFunctionOutcomeProperties
import Solcore.Syntax.DeclarativeYulNamesExactnessProperties

/-! Exact ASTs and source-order signatures of inline-Yul function statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Yul parameter lists fix their names and complete covering span. -/
theorem YulParametersOrdinaryParses.value_unique
    {input : Remainder} {left right : DelimitedList Syntax.YulIdentifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulParametersOrdinaryParses input left afterLeft)
    (rightParsed : YulParametersOrdinaryParses input right afterRight) : left = right :=
  TrailingDelimitedListParses.value_unique yulNameExactOutcomeSpec leftParsed rightParsed

/-- A return clause fixes its arrow, source-order names, and covering span. -/
theorem YulReturnClauseOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnClauseOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnClauseOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftArrow leftNames =>
      cases rightParsed with
      | parsed rightSpan rightArrow rightNames =>
          rcases leftArrow.result_unique rightArrow with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases leftNames.value_unique rightNames
          rfl

/-- Optional returns fix the absent/present branch and complete return clause. -/
theorem YulReturnsOrdinaryParses.value_unique
    {input : Remainder} {left right : Option Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnsOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnsOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          cases rightClause with
          | parsed _ rightToken _ => exact False.elim (leftAbsent ⟨_, rightToken.1⟩)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftClause with
          | parsed _ leftToken _ => exact False.elim (rightAbsent ⟨_, leftToken.1⟩)
      | present rightClause => exact congrArg some (leftClause.value_unique rightClause)

/-- Exact recursive blocks fix the complete ordinary Yul function AST. -/
theorem YulFunctionStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulFunctionStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulFunctionStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftBodySpan leftMarker leftName leftParameters leftReturns leftBody =>
      cases rightParsed with
      | parsed rightSpan rightBodySpan rightMarker rightName rightParameters rightReturns rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftName.result_unique rightName with ⟨nameEq, nameOutputEq⟩
          subst nameEq
          subst nameOutputEq
          have parametersEq := leftParameters.value_unique rightParameters
          have parametersOutputEq := leftParameters.output_unique rightParameters
          subst parametersEq
          subst parametersOutputEq
          have returnsEq := leftReturns.value_unique rightReturns
          have returnsOutputEq := leftReturns.output_unique rightReturns
          subst returnsEq
          subst returnsOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
