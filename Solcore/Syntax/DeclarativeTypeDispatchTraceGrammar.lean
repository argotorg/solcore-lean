import Solcore.Syntax.DeclarativeTypeDispatchSelectionGrammar
import Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeTraceGrammar
import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar

/-! One independent prioritized type layer over arbitrary nested trace
relations. Raw forms remain separate from selection; final rejection emits no
event and reports only the type-expression expectation. No existence is claimed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TypeDispatchFinalTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input : Remainder} {report : ParseDiagnostic}
      (reported : RejectAtReports source endByte { head := .typeExpr, tail := [] } .typeExpr input report) :
      TypeDispatchFinalTraceRejects source endByte input input report []

def TypeDispatchRawTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (branch : TypeDispatchBranch) :
    SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop :=
  match branch with
  | .function => FunctionTypeTraceParses elementTrace
  | .comptime => ComptimeTypeTraceParses elementTrace
  | .mapping => MappingTypeTraceParses elementTrace
  | .proxy => ProxyTypeTraceParses elementTrace
  | .tuple => TupleTypeTraceParses elementTrace
  | .named => NamedTypeTraceParses elementTrace
  | .final => fun _ _ _ _ _ _ => False

def TypeDispatchRawTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (branch : TypeDispatchBranch) :
    SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop :=
  match branch with
  | .function => FunctionTypeTraceRejects elementTrace elementRejects
  | .comptime => ComptimeTypeTraceRejects elementTrace elementRejects
  | .mapping => MappingTypeTraceRejects elementTrace elementRejects
  | .proxy => ProxyTypeTraceRejects elementRejects
  | .tuple => TupleTypeTraceRejects elementTrace elementRejects
  | .named => NamedTypeTraceRejects elementTrace elementRejects
  | .final => TypeDispatchFinalTraceRejects

inductive TypeDispatchTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | selected {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
      (branch : TypeDispatchBranch)
      (selection : TypeDispatchSelects input branch)
      (parsed : TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace) :
      TypeDispatchTraceParses elementTrace source endByte input value output trace

inductive TypeDispatchTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | selected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (branch : TypeDispatchBranch)
      (selection : TypeDispatchSelects input branch)
      (rejection : TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte
        input rejected report trace) :
      TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
