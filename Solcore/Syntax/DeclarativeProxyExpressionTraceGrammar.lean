import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent proxy traces retain the exact marker and nested type AST.
Only the nested type contributes events; no silence or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyExpressionTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker output : Remainder} {type : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeTrace source endByte afterMarker type output trace) :
      ProxyExpressionTraceParses typeTrace source endByte input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output trace

end Solcore.Syntax.DeclarativeGrammar
