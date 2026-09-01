import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeGrammar

/-! Deterministic ordinary outcomes for a guarded Core proxy leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Ordinary proxy success has the unique output of its nested type. -/
theorem ProxyExpressionOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ProxyExpressionOrdinaryParses typeOrdinary input left
      afterLeft)
    (rightParsed : ProxyExpressionOrdinaryParses typeOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftTypeParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightTypeParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          exact typeOutcomes.successOutputUnique leftTypeParsed
            rightTypeParsed

/-- Nested type rejection excludes every ordinary proxy success. -/
theorem ProxyExpressionRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : ProxyExpressionRejects typeRejects input rejected) :
    ¬ ∃ expression output,
      ProxyExpressionOrdinaryParses typeOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | typeRejected rejectedMarkerSpan rejectedMarkerParsed rejectedType =>
      cases successful with
      | parsed successfulMarkerSpan successfulMarkerParsed successfulType =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact typeOutcomes.successRejectDisjoint rejectedType
            ⟨_, _, successfulType⟩

/-- Guarded proxy success and nested type rejection are deterministic and
exclusive whenever the supplied type outcome is. -/
theorem proxyExpressionDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (ProxyExpressionOrdinaryParses typeOrdinary)
      (ProxyExpressionRejects typeRejects) where
  successOutputUnique :=
    ProxyExpressionOrdinaryParses.output_unique typeOutcomes
  successRejectDisjoint :=
    ProxyExpressionRejects.disjointOrdinary typeOutcomes

/-- The existing clean proxy grammar embeds through any supplied clean-to-
ordinary type bridge. -/
theorem ProxyExpressionParses.toOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (typeCleanToOrdinary : ∀ {input type output},
      TypeExprParses input type output → typeOrdinary input type output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ProxyExpressionParses input expression output) :
    ProxyExpressionOrdinaryParses typeOrdinary input expression output := by
  cases parsed with
  | parsed markerSpan markerParsed typeParsed =>
      exact .parsed markerSpan markerParsed (typeCleanToOrdinary typeParsed)

end Solcore.Syntax.DeclarativeGrammar
