import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary success and exact guarded rejection for a Core
proxy-expression leaf.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success of the guarded `@` branch over a supplied type
relation. -/
inductive ProxyExpressionOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {type : Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (typeParsed : typeOrdinary afterMarker type output) :
      ProxyExpressionOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output

/-- Exact rejection inside the guarded proxy branch.  Marker absence belongs
to the enclosing atom dispatcher's failed `@` guard; once selected, only the
nested type parser can reject. -/
inductive ProxyExpressionRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (typeRejected : typeRejects afterMarker rejected) :
      ProxyExpressionRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
