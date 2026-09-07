import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Raw proxy-type success keeps the exact marker, complete nested type, and
covering span. The nested relation alone contributes ordered diagnostic events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker output : Remainder} {inner : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeTrace source endByte afterMarker inner output trace) :
      ProxyTypeTraceParses typeTrace source endByte input {
        span := SourceSpan.cover markerSpan inner.span
        value := .proxy markerSpan inner
      } output trace

end Solcore.Syntax.DeclarativeGrammar
