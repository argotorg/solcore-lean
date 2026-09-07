import Solcore.Syntax.DeclarativeLambdaParameterRawTraceGrammar

/-! Exact pair-selected lambda-parameter outcomes before public recovery.
Both success and rejection retain the same explicit lookahead choice. A raw
comptime failure is never admitted through an absent contextual-name pair. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterCoreTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | ordinary {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (parsed : OrdinaryLambdaParameterTraceParses source endByte input value output trace) :
      LambdaParameterCoreTraceParses source endByte input value output trace
  | comptime {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (parsed : ComptimeLambdaParameterTraceParses source endByte input value output trace) :
      LambdaParameterCoreTraceParses source endByte input value output trace

inductive LambdaParameterCoreTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | ordinary {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (absent : ComptimeParameterPrefixAbsentAt input)
      (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace) :
      LambdaParameterCoreTraceRejects source endByte input rejected report trace
  | comptime {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (present : ComptimeLambdaParameterStartsAt input)
      (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
      LambdaParameterCoreTraceRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
