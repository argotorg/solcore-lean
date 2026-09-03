import Solcore.Syntax.DeclarativeIsolatedBlockTraceProperties

/-! Independent consumers of isolation trace exactness. Child and parent byte
boundaries remain separate, and captured failure is committed once after its events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIsolatedBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}
  {source : SourceId} {parentEndByte : Nat}

example (innerOutcomes : ∀ childEndByte,
    BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte) :
    BlockTraceExactOutcomeSpec (IsolatedBlockTraceParses blockParses blockRejects)
      (IsolatedBlockTraceRejects blockRejects) source parentEndByte :=
  isolatedBlockTraceExactOutcomeSpec innerOutcomes

example (innerOutcomes : ∀ childEndByte,
    BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte)
    {input leftOutput rightOutput : Remainder} {left right : Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input left leftOutput leftTrace)
    (rightParsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input right rightOutput rightTrace) :
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace :=
  leftParsed.result_unique innerOutcomes rightParsed

example (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source parentEndByte)
    {input leftOutput rightOutput : Remainder}
    {leftReport rightReport : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input leftOutput leftReport leftTrace)
    (rightRejected : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rightOutput rightReport rightTrace) :
    leftOutput = rightOutput ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  leftRejected.result_unique innerOutcomes rightRejected

example (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source parentEndByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rejected diagnostic trace) :
    ¬ ∃ body output events, IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input body output events :=
  rejection.disjoint_success innerOutcomes

/-- A child failure uses capture.endByte and becomes an exact empty-block
success at the parent's resume point, preserving duplicate earlier events. -/
theorem recovered_child_appends_once
    {input childRejected : Remainder} {capture : BalancedBlockCapture}
    {event diagnostic : ParseDiagnostic}
    (captured : BalancedBlockCaptures input capture)
    (rejected : blockRejects source capture.endByte (capture.childRemainder input)
      childRejected diagnostic [event, event]) :
    IsolatedBlockTraceParses blockParses blockRejects source parentEndByte input
      { span := capture.span, value := [] } (capture.parentRemainder input)
      [event, event, diagnostic] :=
  .recovered captured rejected

/-- Any competing successful derivation has this recovered AST, exact parent
resume point, and complete child trace followed by its one committed report. -/
theorem recovered_result_is_unique
    (innerOutcomes : ∀ childEndByte,
      BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte)
    {input childRejected output : Remainder} {capture : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic} {body : Block}
    (captured : BalancedBlockCaptures input capture)
    (rejected : blockRejects source capture.endByte (capture.childRemainder input)
      childRejected diagnostic trace)
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input body output events) :
    body = { span := capture.span, value := [] } ∧
      output = capture.parentRemainder input ∧ events = trace ++ [diagnostic] :=
  parsed.result_unique innerOutcomes (.recovered captured rejected)

/-- Once capture exists, no external rejection escapes the isolation wrapper,
even without inner exactness or a successful child derivation. -/
theorem captured_cannot_escape_rejection
    {input rejected : Remainder} {capture : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input capture) :
    ¬ IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rejected diagnostic trace := by
  intro rejection
  cases rejection with
  | direct absent childRejected => exact absent ⟨capture, captured⟩

end Solcore.Test.SyntaxIsolatedBlockTraceProperties
