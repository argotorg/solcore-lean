import Solcore.SourceSemantics.CoreLowering.CallableIndexedCaptureEnvironment

/-! Protected allocation snapshots survive actual source writes and distinct
administrative writes. Capture proofs preserve ordered aliases, including
hidden match slots, and actual accepted callbacks supply allocation code. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedSnapshots
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory GeneralHeap
open CallableIndexedSnapshots CallableIndexedAllocationCompletion

/-- The source payload, mutable context and a fresh helper can all change
without changing the allocation-time snapshot or its carried history. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {native : NativeFrame}
    {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries inputs table native ghost metadata) :
    Holds inputs table layout [3]
      [.bool true, SourceCoreCallableIndexedFrames.encode layout native, .unit,
        .inRight .unit (.bool true), .integer 7]
      ⟨1, native, ghost, metadata⟩ := by
  have initial := completed (layout := layout) (before := [.unit]) (mapping := []) history
    (by intro location impossible; cases impossible) .unit (.inRight .unit (.bool false))
  have sourceUpdated : Holds inputs table layout [3]
      [.unit, SourceCoreCallableIndexedFrames.encode layout native, .unit, .inRight .unit (.bool true)]
      ⟨1, native, ghost, metadata⟩ :=
    initial.source_write (location := 3) (by simp) rfl
  have contextUpdated : Holds inputs table layout [3]
      [.bool true, SourceCoreCallableIndexedFrames.encode layout native, .unit, .inRight .unit (.bool true)]
      ⟨1, native, ghost, metadata⟩ :=
    sourceUpdated.other_write (location := 0) (by change (1 : Nat) ≠ 0; decide) rfl
  exact contextUpdated.fresh_write (suffix := [.unit]) (offset := 0) rfl

/-- An administrative snapshot reference can physically occupy the temporary
slot zero while the generated capture expression still preserves both aliases. -/
example (first hidden : Resolved.LocalId) (inserted : Value) (store : Store) :
    Evaluates [inserted, .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0] store
      (SourceCoreSourceCells.captures (fun index => index + 1) [(first, .word), (hidden, .word)])
      (.pair (.cellRef (OptionalCell.cellType .word) 0) (.cellRef (OptionalCell.cellType .word) 0)) store := by
  exact (Captures.cons rfl (.singleton rfl)).evaluates store

/-- Scope alignment, including a hidden internal slot, supplies all native
capture lookups without requiring a capture execution as a premise. -/
example (catalog : SourceCoreDataCatalog.Catalog) (first hidden : Resolved.LocalId)
    (inserted : Value) :
    ∃ captured,
      Captures [.cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0]
        Renaming.id [(first, .word), (hidden, .word)] captured ∧
      Captures [inserted, .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0]
        (fun index => index + 1) [(first, .word), (hidden, .word)] captured := by
  have reference : ReferenceRepresents [0] [OptionalCell.cellType .word] ⟨0⟩ 0 .word := ⟨rfl, rfl⟩
  have related : DataHeap.EnvRepresents catalog [0] [OptionalCell.cellType .word] []
      [(first, .word), (hidden, .word)] [(first, ⟨0⟩)]
      [.cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0] :=
    .cons reference (.internal reference (by intro location impossible; cases impossible) (.nil .nil))
  exact CallableIndexedCaptureEnvironment.captures_inserted related (fun found => found) inserted

/-- A real successful callback plus an already evaluated payload is enough
to derive completion; the payload may itself be an existing captured closure.
No child allocation evaluation or first-order-store restriction is supplied. -/
example {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError) request = .ok code)
    {payload : Value} {tail : Environment} {before : Store} {location : Location} {native : NativeFrame}
    (scope : request.scope = []) (initializer : request.payload = some (.var 0))
    (reference : (payload :: tail)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ marker,
      Evaluates (payload :: tail) before code
        (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inRight .unit payload]) := by
  obtain ⟨allocation, annotation, same, exactCode⟩ := accepted_receipts onError accepted
  subst code
  refine ⟨SourceCoreHeapMarkers.markerValue allocation.entry.layout .unit, ?_⟩
  have selected : Captures (payload :: tail) request.references request.scope .unit := by rw [scope]; exact .nil
  exact evaluates allocation annotation same reference read selected (.initialized initializer rfl)

/-- A whole-body semantic frame transports the allocation-time metadata even
when execution adds source cells and administrative closures of arbitrary type. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap}
    {before after : Store} {records : List Record}
    (snapshots : All inputs table layout mapping before records)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    All inputs table layout futureMapping after records := snapshots.transport frame

end Solcore.Test.SourceCoreCallableIndexedSnapshots
