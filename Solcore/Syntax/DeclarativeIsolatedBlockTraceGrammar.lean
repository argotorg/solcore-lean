import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent diagnostic traces through balanced block isolation. Inner
judgments carry source and end-byte context explicitly: a captured child uses
its own closing-byte boundary, while the parent retains its original window.
Only recovered child rejection appends the previously uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact successful isolation over abstract inner block trace judgments. -/
inductive IsolatedBlockTraceParses
    (blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
      List ParseDiagnostic → Prop)
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop where
  | direct {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockParses source endByte input body output trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input body output trace
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture} {trace : List ParseDiagnostic}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockParses source capture.endByte
        (capture.childRemainder input) body childOutput trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input body
        (capture.parentRemainder input) trace
  | recovered {input childRejected : Remainder} {capture : BalancedBlockCapture}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyRejected : blockRejects source capture.endByte
        (capture.childRemainder input) childRejected diagnostic trace) :
      IsolatedBlockTraceParses blockParses blockRejects source endByte input
        { span := capture.span, value := [] } (capture.parentRemainder input)
        (trace ++ [diagnostic])

/-- An uncaptured rejection escapes with exactly its original report and
trace. Captured ordinary rejection is a success of the recovery wrapper. -/
inductive IsolatedBlockTraceRejects
    (blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | direct {input rejected : Remainder} {diagnostic : ParseDiagnostic}
      {trace : List ParseDiagnostic}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyRejected : blockRejects source endByte input rejected diagnostic trace) :
      IsolatedBlockTraceRejects blockRejects source endByte input rejected diagnostic trace

end Solcore.Syntax.DeclarativeGrammar
