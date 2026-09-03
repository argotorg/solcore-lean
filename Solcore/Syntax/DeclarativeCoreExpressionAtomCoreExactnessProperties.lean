import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionLambdaExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionSimpleAtomExactnessProperties
import Solcore.Syntax.DeclarativeCoreParenthesizedExactnessProperties

/-! Exact successful ASTs of the seven ordered Core expression-atom branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered branch selection and exact subordinates fix the complete atom-core AST. -/
theorem ExpressionAtomCoreOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 12) [LiteralExpressionOrdinaryParses.value_unique,
      IdentifierExpressionOrdinaryParses.value_unique,
      DotConstructorOrdinaryParses.value_unique nestedOutcomes,
      ProxyExpressionOrdinaryParses.value_unique typeOutcomes,
      ParenthesizedExpressionOrdinaryParses.value_unique nestedOutcomes,
      ArrayLiteralExpressionOrdinaryParses.value_unique nestedOutcomes,
      LambdaExpressionOrdinaryParses.value_unique parameterOutcomes typeOutcomes blockOutcomes,
      LiteralExpressionOrdinaryParses.coreLiteralStartsAt,
      IdentifierExpressionOrdinaryParses.expressionNameStartsAt,
      DotConstructorOrdinaryParses.marker_present,
      ProxyExpressionOrdinaryParses.marker_present,
      ParenthesizedExpressionOrdinaryParses.marker_present,
      ArrayLiteralExpressionOrdinaryParses.marker_present, absent_conflicts_token]

/-- Exact atom-core successes fix the complete AST and final remainder. -/
theorem ExpressionAtomCoreOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
      typeOrdinary blockOrdinary input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      parameterOutcomes.toDeterministicOutcomeSpec typeOutcomes.toDeterministicOutcomeSpec
      blockOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
