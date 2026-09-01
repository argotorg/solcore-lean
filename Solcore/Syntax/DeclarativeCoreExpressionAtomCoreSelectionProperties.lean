import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreStarterProperties

/-! Unique branch selection for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The seven successful branches in executable priority order. -/
inductive ExpressionAtomCoreBranch where
  | literal
  | identifier
  | dotConstructor
  | proxy
  | parenthesized
  | array
  | lambda
  deriving DecidableEq

/-- Parser-independent evidence selecting exactly one Core atom branch. -/
inductive ExpressionAtomCoreBranchSelected :
    ExpressionAtomCoreBranch → Remainder → Prop where
  | literal {input : Remainder}
      (starts : CoreLiteralStartsAt input) :
      ExpressionAtomCoreBranchSelected .literal input
  | identifier {input : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (starts : ExpressionNameStartsAt input) :
      ExpressionAtomCoreBranchSelected .identifier input
  | dotConstructor {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .dot }) :
      ExpressionAtomCoreBranchSelected .dotConstructor input
  | proxy {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .at }) :
      ExpressionAtomCoreBranchSelected .proxy input
  | parenthesized {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .leftParen }) :
      ExpressionAtomCoreBranchSelected .parenthesized input
  | array {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .symbol .leftBracket }) :
      ExpressionAtomCoreBranchSelected .array input
  | lambda {input : Remainder} (markerSpan : SourceSpan)
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan, value := .keyword .lamKw }) :
      ExpressionAtomCoreBranchSelected .lambda input

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered guard evidence selects a unique branch. -/
theorem ExpressionAtomCoreBranchSelected.branch_unique
    {left right : ExpressionAtomCoreBranch} {input : Remainder}
    (leftSelected : ExpressionAtomCoreBranchSelected left input)
    (rightSelected : ExpressionAtomCoreBranchSelected right input) :
    left = right := by
  cases leftSelected with
  | literal leftLiteral =>
      cases rightSelected with
      | literal => rfl
      | identifier rightAbsent _ => exact False.elim (rightAbsent leftLiteral)
      | dotConstructor _ rightAbsent _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | proxy _ rightAbsent _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | parenthesized _ rightAbsent _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | array _ rightAbsent _ _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
      | lambda _ rightAbsent _ _ _ _ _ _ =>
          exact False.elim (rightAbsent leftLiteral)
  | identifier leftLiteralAbsent leftName =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier => rfl
      | dotConstructor _ _ rightNameAbsent _ =>
          exact False.elim (rightNameAbsent leftName)
      | proxy _ _ rightNameAbsent _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | parenthesized _ _ rightNameAbsent _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | array _ _ rightNameAbsent _ _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
      | lambda _ _ rightNameAbsent _ _ _ _ _ =>
          exact False.elim (rightNameAbsent leftName)
  | dotConstructor leftSpan leftLiteralAbsent leftNameAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor => rfl
      | proxy _ _ _ rightDotAbsent _ =>
          exact False.elim (absent_conflicts_token rightDotAbsent leftMarker)
      | parenthesized _ _ _ rightDotAbsent _ _ =>
          exact False.elim (absent_conflicts_token rightDotAbsent leftMarker)
      | array _ _ _ rightDotAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token rightDotAbsent leftMarker)
      | lambda _ _ _ rightDotAbsent _ _ _ _ =>
          exact False.elim (absent_conflicts_token rightDotAbsent leftMarker)
  | proxy leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy => rfl
      | parenthesized _ _ _ _ rightAtAbsent _ =>
          exact False.elim (absent_conflicts_token rightAtAbsent leftMarker)
      | array _ _ _ _ rightAtAbsent _ _ =>
          exact False.elim (absent_conflicts_token rightAtAbsent leftMarker)
      | lambda _ _ _ _ rightAtAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token rightAtAbsent leftMarker)
  | parenthesized leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent
        leftAtAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized => rfl
      | array _ _ _ _ _ rightParenAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightParenAbsent leftMarker)
      | lambda _ _ _ _ _ rightParenAbsent _ _ =>
          exact False.elim
            (absent_conflicts_token rightParenAbsent leftMarker)
  | array leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | array => rfl
      | lambda _ _ _ _ _ _ rightBracketAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightBracketAbsent leftMarker)
  | lambda leftSpan leftLiteralAbsent leftNameAbsent leftDotAbsent leftAtAbsent
        leftParenAbsent leftBracketAbsent leftMarker =>
      cases rightSelected with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral)
      | identifier _ rightName => exact False.elim (leftNameAbsent rightName)
      | dotConstructor _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | proxy _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftAtAbsent rightMarker)
      | parenthesized _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | array _ _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftBracketAbsent rightMarker)
      | lambda => rfl

/-- Every ordinary Core atom success carries some exact branch-selection
evidence.  The existential target keeps elimination proof-irrelevant. -/
theorem ExpressionAtomCoreOrdinaryParses.exists_branch_selected
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input expression output) :
    ∃ branch, ExpressionAtomCoreBranchSelected branch input := by
  cases parsed with
  | literal parsed => exact ⟨.literal, .literal parsed.coreLiteralStartsAt⟩
  | identifier literalAbsent parsed =>
      exact ⟨.identifier,
        .identifier literalAbsent parsed.expressionNameStartsAt⟩
  | dotConstructor literalAbsent nameAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.dotConstructor,
        .dotConstructor span literalAbsent nameAbsent marker⟩
  | proxy literalAbsent nameAbsent dotAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.proxy,
        .proxy span literalAbsent nameAbsent dotAbsent marker⟩
  | parenthesized literalAbsent nameAbsent dotAbsent atAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.parenthesized, .parenthesized span literalAbsent nameAbsent
        dotAbsent atAbsent marker⟩
  | array literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent parsed =>
      rcases parsed.marker_present with ⟨span, marker⟩
      exact ⟨.array, .array span literalAbsent nameAbsent dotAbsent atAbsent
        leftParenAbsent marker⟩
  | lambda literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
        leftBracketAbsent parsed =>
      rcases parsed.marker_present with ⟨span, afterMarker, marker⟩
      exact ⟨.lambda, .lambda span literalAbsent nameAbsent dotAbsent atAbsent
        leftParenAbsent leftBracketAbsent marker.1⟩

/-- The final dispatcher rejection excludes every successful branch
selection. -/
theorem ExpressionAtomCoreFinalRejects.disjointBranchSelected
    {input : Remainder} (rejection : ExpressionAtomCoreFinalRejects input) :
    ¬ ∃ branch, ExpressionAtomCoreBranchSelected branch input := by
  rintro ⟨branch, selected⟩
  cases rejection with
  | final literalAbsent nameAbsent dotAbsent atAbsent leftParenAbsent
        leftBracketAbsent lambdaAbsent =>
      cases selected with
      | literal starts => exact literalAbsent starts
      | identifier _ starts => exact nameAbsent starts
      | dotConstructor span _ _ marker =>
          exact absent_conflicts_token dotAbsent marker
      | proxy span _ _ _ marker =>
          exact absent_conflicts_token atAbsent marker
      | parenthesized span _ _ _ _ marker =>
          exact absent_conflicts_token leftParenAbsent marker
      | array span _ _ _ _ _ marker =>
          exact absent_conflicts_token leftBracketAbsent marker
      | lambda span _ _ _ _ _ _ marker =>
          exact absent_conflicts_token lambdaAbsent marker

end Solcore.Syntax.DeclarativeGrammar
