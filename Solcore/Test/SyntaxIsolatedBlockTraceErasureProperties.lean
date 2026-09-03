import Solcore.Syntax.DeclarativeIsolatedBlockTraceErasureProperties

/-! Independent erasure and repeated-isolation consumers. An outer successful
capture does not recommit a failure already recovered by an inner isolation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIsolatedBlockTraceErasureProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}
  {blockOrdinary : Remainder → Block → Remainder → Prop}
  {blockRejected : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

example
    (successErases : ∀ source endByte input body output trace,
      blockParses source endByte input body output trace → blockOrdinary input body output)
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input body output trace) :
    IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejected input body output :=
  parsed.ordinary successErases rejectionErases

example
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source endByte
      input rejected diagnostic trace) :
    IsolatedCoreBlockRejects blockRejected input rejected :=
  rejection.ordinary rejectionErases

/-- A child recovery is a success for its outer isolation. The inner captured
span is retained as the AST, while the outer capture sets the parent endpoint. -/
theorem nested_recovery_commits_report_once
    {input childRejected : Remainder} {outer inner : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (outerCapture : BalancedBlockCaptures input outer)
    (innerCapture : BalancedBlockCaptures (outer.childRemainder input) inner)
    (rejection : blockRejects source inner.endByte
      (inner.childRemainder (outer.childRemainder input)) childRejected diagnostic trace) :
    IsolatedBlockTraceParses (IsolatedBlockTraceParses blockParses blockRejects)
      (IsolatedBlockTraceRejects blockRejects) source endByte input
      { span := inner.span, value := [] } (outer.parentRemainder input)
      (trace ++ [diagnostic]) :=
  .captured outerCapture (.recovered innerCapture rejection)

end Solcore.Test.SyntaxIsolatedBlockTraceErasureProperties
