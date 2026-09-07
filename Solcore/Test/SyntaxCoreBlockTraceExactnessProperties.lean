import Solcore.Syntax.DeclarativeCoreBlockTraceExactnessProperties

/-! Joint raw/isolated trace consumers expose the required statement laws and
retain distinct child byte boundaries, ordinary failures, and recovered events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

example (statements : StatementTraceExactOutcomeSpec
    statementTrace statementRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy statements

example (statements : ∀ childEndByte,
    StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
        (CoreBlockTraceRejects statementTrace statementRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects statementTrace statementRejects policy))
      source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy statements

/-- A raw failure rules out a successful block with any proposed AST or trace. -/
theorem raw_rejection_excludes_every_success
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected report events) :
    ¬ ∃ body output trace, CoreBlockTraceParses statementTrace policy source endByte
      input body output trace :=
  (coreBlockTraceExactOutcomeSpec policy statements).successRejectDisjoint rejection

/-- Once a captured raw failure is recovered, every isolated success has the
captured full span, parent resume point, and events followed by its report once. -/
theorem recovered_raw_block_result_is_fixed
    (statements : ∀ childEndByte,
      StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte)
    {input childRejected output : Remainder} {capture : BalancedBlockCapture}
    {report : ParseDiagnostic} {events trace : List ParseDiagnostic} {body : Block}
    (captured : BalancedBlockCaptures input capture)
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source capture.endByte
      (capture.childRemainder input) childRejected report events)
    (parsed : IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte
      input body output trace) :
    body = { span := capture.span, value := [] } ∧
      output = capture.parentRemainder input ∧ trace = events ++ [report] :=
  (isolatedCoreBlockTraceExactOutcomeSpec policy statements).successResultUnique
    parsed (.recovered captured rejection)

end Solcore.Test.SyntaxCoreBlockTraceExactnessProperties
