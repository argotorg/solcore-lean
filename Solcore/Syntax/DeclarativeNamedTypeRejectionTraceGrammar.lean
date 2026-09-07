import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceGrammar

/-! Raw named-type rejection stops at the qualified name or its optional
arguments. The finishing spelling event occurs only after both succeed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (name : QualifiedNameTraceRejects .typeExpr source endByte input rejected report trace) :
      NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | argumentsRejected {input afterName rejected : Remainder} {name : QualifiedName}
      {report : ParseDiagnostic} {nameEvents argumentEvents : List ParseDiagnostic}
      (nameParsed : QualifiedNameTraceParses source endByte input name afterName nameEvents)
      (arguments : NamedTypeArgumentsTraceRejects elementTrace elementRejects
        source endByte afterName rejected report argumentEvents) :
      NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report
        (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
