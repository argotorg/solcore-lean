import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeGrammar

/-! Exact block-statement traces wrap a raw Core block with required tail
semicolons. No balanced capture, recovery, or parent-window restoration occurs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive BlockStatementTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
      (bodyParsed : CoreBlockTraceParses statementTrace .require source endByte input body output trace) :
      BlockStatementTraceParses statementTrace source endByte input
        { span := body.span, value := .block body.value } output trace

inductive BlockStatementTraceRejects
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input output : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (bodyRejected : CoreBlockTraceRejects statementTrace statementRejects .require
        source endByte input output diagnostic trace) :
      BlockStatementTraceRejects statementTrace statementRejects source endByte
        input output diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
