import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Raw mapping types use a contextual identifier marker and two recursive
children. Delimiters are silent; key events precede value events exactly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def mappingTypeTraceValue (markerSpan openingSpan closingSpan : SourceSpan)
    (key value : Syntax.TypeExpr) : Syntax.TypeExpr := {
  span := SourceSpan.cover markerSpan closingSpan
  value := .mapping markerSpan (SourceSpan.cover openingSpan closingSpan) key value
}

inductive MappingTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterOpening afterKey afterArrow afterValue output : Remainder}
      {key value : Syntax.TypeExpr} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan closingSpan : SourceSpan)
      (markerToken : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (openingToken : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrowToken : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (valueParsed : elementTrace source endByte afterArrow value afterValue valueEvents)
      (closingToken : ExactTokenParses (.symbol .rightParen) afterValue closingSpan output) :
      MappingTypeTraceParses elementTrace source endByte input
        (mappingTypeTraceValue markerSpan openingSpan closingSpan key value) output (keyEvents ++ valueEvents)

end Solcore.Syntax.DeclarativeGrammar
