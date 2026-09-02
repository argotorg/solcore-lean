import Solcore.Syntax.DeclarativePredicateSequenceOutcomeGrammar

/-! Parser-independent exact rejection for optional canonical `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact optional-`where` rejection after its positively guarded marker.

The absent-marker branch is always a nonconsuming success, while a present
marker commits to the prioritized predicate sequence. -/
inductive OptionalWhereClauseRejects : Remainder → Remainder → Prop where
  | predicatesRejected
      {input afterMarker rejected : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.where.spelling)
        input markerSpan afterMarker)
      (predicatesRejected : PredicateSequenceRejects afterMarker rejected) :
      OptionalWhereClauseRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
