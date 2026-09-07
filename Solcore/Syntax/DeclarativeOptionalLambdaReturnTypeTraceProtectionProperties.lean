import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Only supplied protected type events are preserved. The separate final
rejection report has no implied protection property. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalLambdaReturnTypeTraceParses.cascadeFilters
    (typeProtected : ∀ {input type output trace},
      typeTrace source endByte input type output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {type : Option Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ _ type => exact typeProtected type

theorem OptionalLambdaReturnTypeTraceRejects.cascadeFilters
    (typeProtected : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte
      input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | typeRejected _ _ type => exact typeProtected type

end Solcore.Syntax.DeclarativeGrammar
