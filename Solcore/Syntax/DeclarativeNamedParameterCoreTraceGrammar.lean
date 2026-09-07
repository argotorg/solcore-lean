import Solcore.Syntax.DeclarativeNamedParameterRawTraceGrammar

/-! Exact pair-selected function-parameter outcomes before public recovery.
Both success and rejection retain the same explicit lookahead choice. A raw
comptime failure is never admitted through an absent contextual-name pair. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedParameterCoreTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.FunctionParameter → Remainder → List ParseDiagnostic → Prop where
  | ordinary {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (parsed : OrdinaryNamedParameterTraceParses source endByte input value output trace) :
      NamedParameterCoreTraceParses source endByte input value output trace
  | comptime {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (parsed : ComptimeNamedParameterTraceParses source endByte input value output trace) :
      NamedParameterCoreTraceParses source endByte input value output trace

inductive NamedParameterCoreTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | ordinary {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace) :
      NamedParameterCoreTraceRejects source endByte input rejected report trace
  | comptime {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
      NamedParameterCoreTraceRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
