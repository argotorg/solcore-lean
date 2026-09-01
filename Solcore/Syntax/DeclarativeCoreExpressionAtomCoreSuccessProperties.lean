import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreSelectionProperties
import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeProperties

/-! Output functionality of the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered Core atom ordinary success has a unique output remainder whenever
all supplied subordinate outcomes do. -/
theorem ExpressionAtomCoreOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input left afterLeft)
    (rightParsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | literal leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact literalExpressionDeterministicOutcomeSpec.successOutputUnique
            leftBranch rightBranch
      | identifier literalAbsent _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | dotConstructor literalAbsent _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | proxy literalAbsent _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | parenthesized literalAbsent _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | array literalAbsent _ _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
      | lambda literalAbsent _ _ _ _ _ _ =>
          exact False.elim
            (literalAbsent leftBranch.coreLiteralStartsAt)
  | identifier leftLiteralAbsent leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact identifierExpressionDeterministicOutcomeSpec
            |>.successOutputUnique leftBranch rightBranch
      | dotConstructor _ nameAbsent _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | proxy _ nameAbsent _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | parenthesized _ nameAbsent _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | array _ nameAbsent _ _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
      | lambda _ nameAbsent _ _ _ _ _ =>
          exact False.elim
            (nameAbsent leftBranch.expressionNameStartsAt)
  | dotConstructor leftLiteralAbsent leftNameAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          exact (dotConstructorDeterministicOutcomeSpec nestedOutcomes)
            |>.successOutputUnique leftBranch rightBranch
      | proxy _ _ dotAbsent _ =>
          exact False.elim (absent_conflicts_token dotAbsent leftMarker)
      | parenthesized _ _ dotAbsent _ _ =>
          exact False.elim (absent_conflicts_token dotAbsent leftMarker)
      | array _ _ dotAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token dotAbsent leftMarker)
      | lambda _ _ dotAbsent _ _ _ _ =>
          exact False.elim (absent_conflicts_token dotAbsent leftMarker)
  | proxy leftLiteralAbsent leftNameAbsent leftDotAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          exact (proxyExpressionDeterministicOutcomeSpec typeOutcomes)
            |>.successOutputUnique leftBranch rightBranch
      | parenthesized _ _ _ atAbsent _ =>
          exact False.elim (absent_conflicts_token atAbsent leftMarker)
      | array _ _ _ atAbsent _ _ =>
          exact False.elim (absent_conflicts_token atAbsent leftMarker)
      | lambda _ _ _ atAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token atAbsent leftMarker)
  | parenthesized leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          exact (parenthesizedExpressionDeterministicOutcomeSpec
            nestedOutcomes).successOutputUnique leftBranch rightBranch
      | array _ _ _ _ leftParenAbsent _ =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent leftMarker)
      | lambda _ _ _ _ leftParenAbsent _ _ =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent leftMarker)
  | array leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBranch =>
      rcases leftBranch.marker_present with ⟨leftSpan, leftMarker⟩
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | array _ _ _ _ _ rightBranch =>
          exact (arrayLiteralExpressionDeterministicOutcomeSpec
            nestedOutcomes).successOutputUnique leftBranch rightBranch
      | lambda _ _ _ _ _ leftBracketAbsent _ =>
          exact False.elim
            (absent_conflicts_token leftBracketAbsent leftMarker)
  | lambda leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBracketAbsent leftBranch =>
      cases rightParsed with
      | literal rightBranch =>
          exact False.elim
            (leftLiteralAbsent rightBranch.coreLiteralStartsAt)
      | identifier _ rightBranch =>
          exact False.elim
            (leftNameAbsent rightBranch.expressionNameStartsAt)
      | dotConstructor _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | array _ _ _ _ _ rightBranch =>
          rcases rightBranch.marker_present with ⟨rightSpan, rightMarker⟩
          exact False.elim
            (absent_conflicts_token leftBracketAbsent rightMarker)
      | lambda _ _ _ _ _ _ rightBranch =>
          exact (lambdaExpressionDeterministicOutcomeSpec parameterOutcomes
            typeOutcomes blockOutcomes).successOutputUnique leftBranch
              rightBranch

end Solcore.Syntax.DeclarativeGrammar
