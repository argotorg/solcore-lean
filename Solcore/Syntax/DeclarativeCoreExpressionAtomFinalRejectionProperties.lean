import Solcore.Syntax.DeclarativeCoreExpressionAtomFinalRejectionGrammar

/-! Exclusivity of the final Core atom dispatcher rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Final dispatcher rejection excludes every successful ordered Core atom
branch, independently of the supplied recursive grammars. -/
theorem ExpressionAtomCoreFinalRejects.disjointCore
    {nestedParses : Remainder → Syntax.Expr → Remainder → Prop}
    {blockParses : Remainder → Syntax.Block → Remainder → Prop}
    {input : Remainder} (rejected : ExpressionAtomCoreFinalRejects input) :
    ¬ ∃ expression output,
      ExpressionAtomCoreParses nestedParses blockParses input expression
        output := by
  rintro ⟨expression, output, parsed⟩
  cases rejected with
  | final literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
      leftBracketAbsent lambdaAbsent =>
      cases parsed with
      | literal parsed =>
          cases parsed with
          | parsed literalParsed =>
              cases literalParsed with
              | decimal token =>
                  exact literalAbsent (Or.inl ⟨_, _, token⟩)
              | hexadecimal token =>
                  exact literalAbsent (Or.inr (Or.inl ⟨_, _, token⟩))
              | string token =>
                  exact literalAbsent (Or.inr (Or.inr ⟨_, _, token⟩))
      | identifier earlierLiteralAbsent parsed =>
          cases parsed with
          | parsed nameParsed =>
              cases nameParsed with
              | boolean booleanParsed =>
                  cases booleanParsed with
                  | trueKeyword token =>
                      exact nameAbsent (Or.inl ⟨_, token⟩)
                  | falseKeyword token =>
                      exact nameAbsent (Or.inr (Or.inl ⟨_, token⟩))
              | identifier trueAbsent falseAbsent identifierParsed =>
                  exact nameAbsent
                    (Or.inr (Or.inr ⟨_, _, identifierParsed.1⟩))
      | dotConstructor earlierLiteralAbsent earlierNameAbsent parsed =>
          cases parsed with
          | parsed dotSpan dotParsed nameParsed argumentsParsed =>
              exact absent_conflicts_token dotAbsent dotParsed.1
      | proxy earlierLiteralAbsent earlierNameAbsent earlierDotAbsent parsed =>
          cases parsed with
          | parsed markerSpan markerParsed typeParsed =>
              exact absent_conflicts_token atAbsent markerParsed.1
      | parenthesized earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent parsed =>
          cases parsed with
          | empty openingSpan closingSpan openingParsed closingParsed =>
              exact absent_conflicts_token leftParenAbsent openingParsed.1
          | group openingSpan closingSpan openingParsed nestedParsed
              elementParsed progress commaAbsent closingParsed =>
              exact absent_conflicts_token leftParenAbsent openingParsed.1
          | tuple openingSpan closingSpan openingParsed closingAbsent
              firstParsed progress tail =>
              exact absent_conflicts_token leftParenAbsent openingParsed.1
      | array earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent earlierLeftParenAbsent parsed =>
          cases parsed with
          | parsed valuesParsed =>
              cases valuesParsed with
              | empty openingSpan closingSpan openingToken closingToken =>
                  exact absent_conflicts_token leftBracketAbsent openingToken
              | nonempty closingAbsent nonemptyParsed =>
                  rcases nonemptyParsed with
                    ⟨openingSpan, first, afterFirst, rest, closingSpan,
                      tokensEq, endIndexEq, openingToken, firstParsed,
                      progress, tail, elementsEq, spanEq⟩
                  exact absent_conflicts_token leftBracketAbsent
                    openingToken
      | lambda earlierLiteralAbsent earlierNameAbsent earlierDotAbsent
          earlierAtAbsent earlierLeftParenAbsent earlierLeftBracketAbsent
          parsed =>
          cases parsed with
          | parsed markerSpan markerParsed parametersParsed returnTypeParsed
              bodyParsed =>
              exact absent_conflicts_token lambdaAbsent markerParsed.1

end Solcore.Syntax.DeclarativeGrammar
