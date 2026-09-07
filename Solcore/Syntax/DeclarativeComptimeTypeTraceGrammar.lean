import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Raw comptime-type traces retain every source-shaped AST component. The
contextual marker is its actual identifier token; only the child emits events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def comptimeTypeTraceValue (markerSpan openingSpan closingSpan : SourceSpan)
    (inner : Syntax.TypeExpr) : Syntax.TypeExpr := {
  span := SourceSpan.cover markerSpan closingSpan
  value := .comptime markerSpan (SourceSpan.cover openingSpan closingSpan) inner
}

inductive ComptimeTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterOpening afterInner output : Remainder} {inner : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan openingSpan closingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementTrace source endByte afterOpening inner afterInner trace)
      (closing : ExactTokenParses (.symbol .greater) afterInner closingSpan output) :
      ComptimeTypeTraceParses elementTrace source endByte input
        (comptimeTypeTraceValue markerSpan openingSpan closingSpan inner) output trace

end Solcore.Syntax.DeclarativeGrammar
