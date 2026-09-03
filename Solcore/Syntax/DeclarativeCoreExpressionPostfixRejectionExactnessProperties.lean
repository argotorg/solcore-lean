import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties

/-! Exact postfix rejection endpoints, independent of the accumulated base AST. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem postfix_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem postfix_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Exact nested outcomes fix every postfix rejection endpoint independently
of the accumulated base, retaining index/call/field selection priority. -/
theorem PostfixTailRejects.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input left right : Remainder} {leftBase rightBase : Syntax.Expr}
    (leftRejected : PostfixTailRejects nestedOrdinary nestedRejects input
      leftBase left)
    (rightRejected : PostfixTailRejects nestedOrdinary nestedRejects input
      rightBase right) : left = right := by
  have argumentsOutcomes := noTrailingDelimitedListExactOutcomeSpec
    .leftParen .rightParen nestedOutcomes
  induction leftRejected generalizing rightBase right <;>
    cases rightRejected <;>
    grind (ematch := 20) [postfix_absent_conflicts_exact,
      postfix_absent_conflicts_token, ExactTokenParses.output_unique,
      nestedOutcomes.successOutputUnique, nestedOutcomes.successRejectDisjoint,
      nestedOutcomes.rejectOutputUnique,
      NoTrailingDelimitedListParses.opening_present,
      argumentsOutcomes.successOutputUnique,
      argumentsOutcomes.successRejectDisjoint,
      argumentsOutcomes.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique]

/-- Exact atom and nested outcomes fix the first rejecting endpoint of the
complete atom-plus-postfix sequence. -/
theorem ExpressionPostfixRejects.output_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input left right : Remainder}
    (leftRejected : ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input left)
    (rightRejected : ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input right) : left = right := by
  cases leftRejected with
  | atomRejected leftAtom =>
      cases rightRejected with
      | atomRejected rightAtom =>
          exact atomOutcomes.rejectOutputUnique leftAtom rightAtom
      | tailRejected rightAtom rightTail =>
          exact False.elim
            (atomOutcomes.successRejectDisjoint leftAtom ⟨_, _, rightAtom⟩)
  | tailRejected leftAtom leftTail =>
      cases rightRejected with
      | atomRejected rightAtom =>
          exact False.elim
            (atomOutcomes.successRejectDisjoint rightAtom ⟨_, _, leftAtom⟩)
      | tailRejected rightAtom rightTail =>
          have inputEq := atomOutcomes.successOutputUnique leftAtom rightAtom
          subst inputEq
          exact leftTail.output_unique nestedOutcomes rightTail

end Solcore.Syntax.DeclarativeGrammar
