import Solcore.Syntax.DeclarativeCorePatternComptimeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Parser-independent ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary compile-time-pattern success has the same exact token shape as
the clean grammar while permitting an ordinary supplied expression. -/
abbrev ComptimePatternOrdinaryParses := ComptimePatternParses

/-- Exact rejection is either the non-consuming missing marker or rejection
of the supplied expression after the exact contextual marker. -/
inductive ComptimePatternRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling)) :
      ComptimePatternRejects expressionRejects input input
  | expressionRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (rejectedExpression : expressionRejects afterMarker rejected) :
      ComptimePatternRejects expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
