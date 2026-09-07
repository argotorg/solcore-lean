import Solcore.Syntax.DeclarativeParameterRecoveryTraceGrammar

/-! Standalone lambda recovery reuses the independent function recovery scan,
retagging its recovered span as a lambda error. The event and terminal report
are unchanged; a caller's earlier failure commitment is outside this grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive LambdaParameterRecoveryTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.LambdaParameter → Remainder → List ParseDiagnostic → Prop where
  | recovered {input output : Remainder} {parameter : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
      (parsed : FunctionParameterRecoveryTraceParses source endByte input parameter output trace) :
      LambdaParameterRecoveryTraceParses source endByte input { span := parameter.span, value := .error } output trace

abbrev LambdaParameterRecoveryTraceRejects := FunctionParameterRecoveryTraceRejects

end Solcore.Syntax.DeclarativeGrammar
