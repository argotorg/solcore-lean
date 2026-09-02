import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Parser-independent exact rejection for optional canonical `returns`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact optional-`returns` rejection after its positively guarded marker.

The absent-marker branch is always a nonconsuming success, while a present
marker commits to the allow-empty, allow-trailing return-type list. -/
inductive OptionalReturnClauseRejects : Remainder → Remainder → Prop where
  | typesRejected
      {input afterMarker rejected : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.returns.spelling)
        input markerSpan afterMarker)
      (typesRejected : DelimitedListRejects .leftParen .rightParen true true
        TypeExprOrdinaryParses TypeExprRejects afterMarker rejected) :
      OptionalReturnClauseRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
