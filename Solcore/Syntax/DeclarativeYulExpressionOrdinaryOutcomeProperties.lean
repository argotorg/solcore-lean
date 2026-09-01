import Solcore.Syntax.DeclarativeYulExpressionOrdinaryCoreProperties

/-!
Functionality, rejection exclusivity, and the deterministic outcome contract
for recovering ordinary inline-Yul expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

private def tokenKindStartsOrdinaryYulExpression : TokenKind → Bool
  | .decimalLiteral _
  | .hexadecimalLiteral _
  | .stringLiteral _
  | .keyword .trueKw
  | .keyword .falseKw
  | .identifier _
  | .yulIdentifier _
  | .symbol .underscore
  | .keyword .fallbackKw
  | .yulMetaBacktick _
  | .yulMetaInterpolation _ => true
  | _ => false

/-- Every ordinary core success exposes a classified current token. -/
private theorem YulExpressionCoreOrdinaryParses.current_token
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input expression output) :
    ∃ token,
      TokenAt input.tokens input.endIndex input.cursor token ∧
        tokenKindStartsOrdinaryYulExpression token.value = true := by
  cases parsed with
  | literal parsed =>
      cases parsed with
      | decimal token
      | hexadecimal token
      | string token
      | trueKeyword token
      | falseKeyword token => exact ⟨_, token, rfl⟩
  | named literalAbsent parsed =>
      cases parsed with
      | identifier nameParsed argumentsParsed
      | call nameParsed argumentsParsed =>
          cases nameParsed with
          | marked token
          | underscore token
          | fallbackKeyword token => exact ⟨_, token, rfl⟩
          | identifier parsed => exact ⟨_, parsed.1, rfl⟩
  | metaBacktick literalAbsent nameAbsent token => exact ⟨_, token, rfl⟩
  | metaInterpolation literalAbsent nameAbsent token =>
      exact ⟨_, token, rfl⟩

/-- The final core rejection guard excludes every ordinary core success. -/
theorem YulExpressionCoreFinalRejects.disjointOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input : Remainder} (rejected : YulExpressionCoreFinalRejects input) :
    ¬ ∃ expression output,
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  cases rejected with
  | final literalAbsent nameAbsent metaAbsent =>
      cases parsed with
      | literal parsed => exact literalAbsent parsed.startsAt
      | named otherLiteralAbsent parsed => exact nameAbsent parsed.startsAt
      | metaBacktick otherLiteralAbsent otherNameAbsent token =>
          exact metaAbsent (Or.inl ⟨_, _, token⟩)
      | metaInterpolation otherLiteralAbsent otherNameAbsent token =>
          exact metaAbsent (Or.inr ⟨_, _, token⟩)

/-- A recovery scan has functional output from a fixed current remainder. -/
theorem YulExpressionRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder},
      YulExpressionRecoveryScanParses first leftLast input left afterLeft →
      YulExpressionRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight
    leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- One ordinary recovering expression layer has functional output. -/
theorem YulExpressionLayerOrdinaryParses.output_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.output_unique outcomes rightCore
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Inline-Yul expression rejection is non-consuming. -/
theorem YulExpressionRejects.output_eq {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- Binary expression rejection excludes every ordinary core success. -/
theorem YulExpressionRejects.disjointCoreOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) :
    ¬ ∃ expression output,
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  rcases parsed.current_token with ⟨current, currentAt, starts⟩
  cases rejection with
  | windowEnd atEnd => exact (Nat.not_lt_of_ge atEnd) currentAt.1
  | comma boundaryAt
  | rightParen boundaryAt
  | rightBrace boundaryAt =>
      have tokenEq := tokenAt_unique boundaryAt currentAt
      have kindEq := congrArg (fun token : Token => token.value) tokenEq
      rw [← kindEq] at starts
      simp [tokenKindStartsOrdinaryYulExpression] at starts
  | missingToken inside missing =>
      have found := currentAt.2
      rw [missing] at found
      contradiction

/-- Binary expression rejection excludes ordinary recovering-layer success. -/
theorem YulExpressionRejects.disjointLayerOrdinary
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulExpressionRejects input rejected) :
    ¬ ∃ expression output,
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output := by
  rintro ⟨expression, output, parsed⟩
  cases parsed with
  | core parsed =>
      exact rejection.disjointCoreOrdinary ⟨_, _, parsed⟩
  | recovered coreRejected continues current scan =>
      have rejectedEq := rejection.output_eq
      subst rejected
      exact continues rejection

/-- A clean core expression is also a success of the ordinary recovery layer. -/
theorem YulExpressionCoreParses.toOrdinaryLayer
    {ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCoreParses cleanParses
      (YulCallArgumentsFallbackSpec.ofOutcomes ordinaryParses cleanParses
        nestedRejects outcomes cleanToOrdinary)
      input expression output) :
    YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
      expression output :=
  .core (parsed.toOrdinary outcomes cleanToOrdinary)

/-- Construct the deterministic ordinary outcome contract for one recovering
inline-Yul expression layer. -/
theorem yulExpressionDeterministicOutcomeSpec
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects)
      YulExpressionRejects where
  successOutputUnique :=
    YulExpressionLayerOrdinaryParses.output_unique outcomes
  successRejectDisjoint := YulExpressionRejects.disjointLayerOrdinary

end Solcore.Syntax.DeclarativeGrammar
