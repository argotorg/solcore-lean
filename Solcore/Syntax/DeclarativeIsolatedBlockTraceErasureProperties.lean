import Solcore.Syntax.DeclarativeIsolatedBlockTraceGrammar

/-! Trace erasure preserves the existing independent isolation outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Any sound erasure of the inner trace judgments lifts through direct
execution, successful capture, and captured rejection recovery. -/
theorem IsolatedBlockTraceParses.ordinary
    {blockParses : SourceId → Nat → Remainder → Syntax.Block → Remainder →
      List ParseDiagnostic → Prop}
    {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejected : Remainder → Remainder → Prop}
    (successErases : ∀ source endByte input body output trace,
      blockParses source endByte input body output trace → blockOrdinary input body output)
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {body : Syntax.Block} {trace : List ParseDiagnostic}
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input body output trace) :
    IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejected input body output := by
  cases parsed with
  | direct absent bodyParsed => exact .direct absent (successErases _ _ _ _ _ _ bodyParsed)
  | captured capture bodyParsed => exact .captured capture (successErases _ _ _ _ _ _ bodyParsed)
  | recovered capture bodyRejected =>
      exact .recovered capture (rejectionErases _ _ _ _ _ _ bodyRejected)

/-- An escaping rejection erases to the direct, uncaptured ordinary branch. -/
theorem IsolatedBlockTraceRejects.ordinary
    {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
      List ParseDiagnostic → Prop}
    {blockRejected : Remainder → Remainder → Prop}
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source endByte
      input rejected diagnostic trace) :
    IsolatedCoreBlockRejects blockRejected input rejected := by
  cases rejection with
  | direct absent bodyRejected => exact .direct absent (rejectionErases _ _ _ _ _ _ bodyRejected)

end Solcore.Syntax.DeclarativeGrammar
