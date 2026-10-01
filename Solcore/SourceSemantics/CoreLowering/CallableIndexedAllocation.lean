import Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol

/-! Actual source-allocation annotation receipts preserve the insertion of an
indexed frame snapshot. The immediate new cell carries the same ghost metadata.
Future persistence in a completed store is a separate frame invariant; an
arbitrary child evaluation is not assumed unable to overwrite that cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
open Core Frontend CallableIndexedHistory
open CallableAncestryPairedLookup (Inputs)
open SourceCoreCallableIndexedAllocationFrames
open DataEquality (Selects)

theorem allocator_receipt (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request)
    {code : Expr} (accepted : allocator layout globals allocate request = .ok code) :
    ∃ receipt : Annotated layout globals allocate request,
      annotateWithReceipt layout globals allocate request = .ok receipt ∧
      code = snapshotBefore layout (.var (referenceIndex globals request)) receipt.original := by
  unfold allocator at accepted
  cases prepared : annotateWithReceipt layout globals allocate request with
  | error error => simp [prepared, Except.map] at accepted
  | ok receipt =>
    simp only [prepared, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, rfl, accepted.symm.trans receipt.exact⟩

/-- A real successful allocator callback places the exact current carrier in
an administrative cell before running the actual shifted allocation code. -/
theorem annotated_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {layout : Layout} {globals : Nat} {allocate : Allocator} {request : Request}
    (receipt : Annotated layout globals allocate request)
    {environment : Environment} {before after : Store} {result : Value} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (history : Carries inputs table native ghost metadata)
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native])
      (receipt.original.weakenAt 0) result after) :
    Evaluates environment before receipt.expression result after ∧
    CellState inputs table layout before.length native ghost
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) := by
  rw [receipt.exact]
  exact ⟨.letE (.newCell (.loadCell (.var reference) read)) evaluated,
    ⟨by simp [Store.read?], .stable history⟩⟩

/-- Completed emitted annotation exposes the actual child trace under its new
snapshot reference; this inversion does not need a source execution witness. -/
theorem annotated_reflects {layout : Layout} {globals : Nat} {allocate : Allocator} {request : Request}
    (receipt : Annotated layout globals allocate request)
    {environment : Environment} {before after : Store} {result snapshot : Value} {location : Location}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some snapshot)
    (evaluated : Evaluates environment before receipt.expression result after) :
    Evaluates (.cellRef layout.type before.length :: environment) (before ++ [snapshot])
      (receipt.original.weakenAt 0) result after := by
  rw [receipt.exact] at evaluated
  cases evaluated with
  | letE allocated body =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic allocated
      (Evaluates.newCell (.loadCell (.var reference) read))
    exact body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
