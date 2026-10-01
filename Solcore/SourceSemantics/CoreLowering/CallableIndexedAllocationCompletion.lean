import Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
import Solcore.Frontend.SourceCoreAllocationLayouts

/-! Completion of actual marked source allocations retains the preceding
indexed snapshot. Capture and payload expressions select the caller's existing
slots; the snapshot reference is inserted and discarded administratively.
The accepted layout and annotation receipts identify the emitted code, while
explicit lexical slot receipts identify its actual references and payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
open Core Frontend SourceInference CallableIndexedHistory GeneralHeap
open SourceCoreCallableIndexedAllocationFrames

/-- Capture selection records actual lexical references in scope order. -/
inductive Captures (environment : Environment) : Renaming → SourceCoreSourceCells.Scope → Value → Prop where
  | nil {references : Renaming} : Captures environment references [] .unit
  | singleton {references : Renaming} {id : Resolved.LocalId} {type : Ty} {location : Location}
      (found : environment[references 0]? = some (.cellRef (OptionalCell.cellType type) location)) :
      Captures environment references [(id, type)] (.cellRef (OptionalCell.cellType type) location)
  | cons {references : Renaming} {id : Resolved.LocalId} {type : Ty} {location : Location}
      {next : Resolved.LocalId × Ty} {rest : SourceCoreSourceCells.Scope} {tail : Value}
      (found : environment[references 0]? = some (.cellRef (OptionalCell.cellType type) location))
      (remaining : Captures environment (fun index => references (index + 1)) (next :: rest) tail) :
      Captures environment references ((id, type) :: next :: rest) (.pair (.cellRef (OptionalCell.cellType type) location) tail)

theorem Captures.evaluates {environment : Environment} {references : Renaming} {scope : SourceCoreSourceCells.Scope} {captured : Value}
    (selected : Captures environment references scope captured) (store : Store) :
    Evaluates environment store (SourceCoreSourceCells.captures references scope) captured store := by
  induction selected with
  | nil => exact .unit
  | singleton found => exact .var found
  | cons found remaining ih => exact .pair (.var found) ih

theorem Captures.weaken {environment : Environment} {references : Renaming} {scope : SourceCoreSourceCells.Scope} {captured : Value}
    (selected : Captures environment references scope captured) (inserted : Value) :
    Captures (inserted :: environment) (fun index => references index + 1) scope captured := by
  induction selected with
  | nil => exact .nil
  | singleton found => exact .singleton (by simpa using found)
  | cons found remaining ih => exact .cons (by simpa using found) ih

/-- Actual lexical slot lookups construct capture selection; no supplied
capture evaluation is needed. Repeated locations retain their aliases. -/
theorem Captures.of_slots {environment : Environment} (scope : SourceCoreSourceCells.Scope) (references : Renaming)
    (slots : ∀ index binding, scope[index]? = some binding → ∃ location,
      environment[references index]? = some (.cellRef (OptionalCell.cellType binding.2) location)) :
    ∃ captured, Captures environment references scope captured := by
  induction scope generalizing references with
  | nil => exact ⟨.unit, .nil⟩
  | cons head rest ih =>
    obtain ⟨location, found⟩ := slots 0 head rfl
    rcases head with ⟨id, type⟩
    cases rest with
    | nil => exact ⟨_, .singleton found⟩
    | cons next tail =>
      obtain ⟨captured, selected⟩ := ih (fun index => references (index + 1)) (by
        intro index binding selected
        exact slots (index + 1) binding (by simpa using selected))
      exact ⟨_, .cons found selected⟩

/-- A fresh administrative binder shifts every actual selected slot. Its own
slot zero is absent from the shifted capture selector. -/
theorem captures_weaken (references : Renaming) (scope : SourceCoreSourceCells.Scope) :
    (SourceCoreSourceCells.captures references scope).weakenAt 0 =
      SourceCoreSourceCells.captures (fun index => references index + 1) scope := by
  induction scope generalizing references with
  | nil => simp [SourceCoreSourceCells.captures, Expr.weakenAt]
  | cons head rest ih =>
    cases rest with
    | nil => simp [SourceCoreSourceCells.captures, Expr.weakenAt]
    | cons next tail => simp only [SourceCoreSourceCells.captures, Expr.weakenAt, Nat.zero_le, ↓reduceIte, ih]

inductive PayloadAt (request : Request) (environment : Environment) : Option Value → Prop where
  | absent (shape : request.payload = none) : PayloadAt request environment none
  | initialized {value : Value} (shape : request.payload = some (.var 0))
      (found : environment[0]? = some value) : PayloadAt request environment (some value)

def optionalValue (type : Ty) : Option Value → Value
  | none => .inLeft type .unit
  | some value => .inRight .unit value

private theorem allocate_weaken (layout : SourceCoreHeapMarkers.Layout) (type : Ty) (captures : Expr) :
    (SourceCoreHeapMarkers.allocate layout type captures).weakenAt 0 =
      SourceCoreHeapMarkers.allocate layout type (captures.weakenAt 0) := by
  simp [SourceCoreHeapMarkers.allocate, SourceCoreHeapMarkers.marker, OptionalCell.allocate, Expr.weakenAt]

private theorem allocateInitialized_rename (layout : SourceCoreHeapMarkers.Layout) (type : Ty)
    (captures initializer : Expr) (ξ : Renaming) :
    (SourceCoreHeapMarkers.allocateInitialized layout type captures initializer).rename ξ =
      SourceCoreHeapMarkers.allocateInitialized layout type (captures.rename ξ) (initializer.rename ξ) := by
  simp [SourceCoreHeapMarkers.allocateInitialized, SourceCoreHeapMarkers.marker,
    OptionalCell.allocateInitialized, Expr.rename, Renaming.lift]

private theorem allocateInitialized_weaken (layout : SourceCoreHeapMarkers.Layout) (type : Ty)
    (captures initializer : Expr) :
    (SourceCoreHeapMarkers.allocateInitialized layout type captures initializer).weakenAt 0 =
      SourceCoreHeapMarkers.allocateInitialized layout type (captures.weakenAt 0) (initializer.weakenAt 0) := by
  simpa only [Expr.rename_insertion] using allocateInitialized_rename layout type captures initializer (Renaming.insertion 0)

/-- Actual success of the composed allocator provides both sealed receipts,
with the original expression shared by the layout and snapshot annotation. -/
theorem accepted_receipts {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {layout : Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : allocator layout globals (layouts.allocatorAt owner active onError) request = .ok code) :
    ∃ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
      (annotation : Annotated layout globals (layouts.allocatorAt owner active onError) request),
      annotation.original = allocation.expression ∧ code = annotation.expression := by
  obtain ⟨annotation, _, exactCode⟩ := CallableIndexedAllocation.allocator_receipt _ _ _ _ accepted
  have original := annotation.allocated
  have allocated : SourceCoreAllocationLayouts.allocate layouts owner active request = .ok annotation.original := by
    cases result : SourceCoreAllocationLayouts.allocate layouts owner active request with
    | error error => simp [SourceCoreAllocationLayouts.Prepared.allocatorAt, result, Except.mapError] at original
    | ok expression =>
      have same : expression = annotation.original := by
        simpa [SourceCoreAllocationLayouts.Prepared.allocatorAt, result, Except.mapError] using original
      simp only [same]
  obtain ⟨allocation, same⟩ := SourceCoreAllocationLayouts.allocate_receipt allocated
  exact ⟨allocation, annotation, same.symm, exactCode.trans annotation.exact.symm⟩

/-- Actual layout and annotation receipts close the allocation child execution.
The only value inputs are the existing lexical references and an optional
already-evaluated result slot, as emitted by the common source-cell helpers. -/
theorem evaluates {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before : Store} {location : Location} {native : NativeFrame} {captured : Value} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (captures : Captures environment request.references request.scope captured)
    (payloadAt : PayloadAt request environment payload) :
    Evaluates environment before annotation.expression
      (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) := by
  rw [annotation.exact, same, allocation.expressionExact]
  apply Evaluates.letE (.newCell (.loadCell (.var reference) read))
  cases payloadAt with
  | absent shape =>
    simp only [SourceCoreAllocationLayouts.allocation, shape, allocate_weaken, captures_weaken, optionalValue]
    simpa [List.append_assoc, Nat.add_assoc] using
      (SourceCoreHeapMarkers.allocate_evaluates
        ((captures.weaken (.cellRef layout.type before.length)).evaluates
          (before ++ [SourceCoreCallableIndexedFrames.encode layout native])))
  | @initialized value shape found =>
    simp only [SourceCoreAllocationLayouts.allocation, shape, allocateInitialized_weaken, optionalValue]
    have init : Evaluates (.cellRef layout.type before.length :: environment)
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) ((Expr.var 0).weakenAt 0) value
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native]) := by
      simpa [Expr.weakenAt] using (Evaluates.var (index := 1) (by simpa using found))
    have selected := ((captures.weaken (.cellRef layout.type before.length)).weaken value).evaluates
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native])
    rw [← captures_weaken, ← captures_weaken] at selected
    simpa [List.append_assoc, Nat.add_assoc] using
      SourceCoreHeapMarkers.allocateInitialized_evaluates init selected

/-- Any completed run of the authenticated allocation has exactly the three
new cells established above. No child execution is a premise of this result. -/
theorem reflects {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before after : Store} {location : Location} {native : NativeFrame}
    {captured result : Value} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (captures : Captures environment request.references request.scope captured)
    (payloadAt : PayloadAt request environment payload)
    (evaluated : Evaluates environment before annotation.expression result after) :
    result = .cellRef (OptionalCell.cellType request.payloadType) (before.length + 2) ∧
      after = before ++ [SourceCoreCallableIndexedFrames.encode layout native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload] :=
  evaluation_deterministic evaluated (evaluates allocation annotation same reference read captures payloadAt)

/-- The emitted append pattern preserves every old administrative cell, while
only the payload location joins the source mapping. -/
theorem allocation_frame (mapping : LocationMap) (before : Store) (snapshot marker payload : Value) :
    AdministrativePreserved mapping before (mapping ++ [before.length + 2]) (before ++ [snapshot, marker, payload]) := by
  intro location absent bound
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨absent, Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))⟩
  · exact List.getElem?_append_left bound

/-- Whole allocation completion appends a protected snapshot record and
transports every existing one. The source map receives only the payload cell.
All child evaluation is derived from actual allocator/capture/slot receipts. -/
theorem preserves {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : Request} {layout : Layout} {globals : Nat} {allocate : Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : Annotated layout globals allocate request) (same : annotation.original = allocation.expression)
    {environment : Environment} {before : Store} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState} {mapping : LocationMap} {records : List CallableIndexedSnapshots.Record} {payload : Option Value}
    (reference : environment[referenceIndex globals request]? = some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (history : Carries graph.inputs graph.table native ghost metadata)
    (bounded : ∀ location ∈ mapping, location < before.length)
    (snapshots : CallableIndexedSnapshots.All graph.inputs graph.table layout mapping before records)
    (slots : ∀ index binding, request.scope[index]? = some binding → ∃ location,
      environment[request.references index]? = some (.cellRef (OptionalCell.cellType binding.2) location))
    (payloadAt : PayloadAt request environment payload) :
    ∃ captured,
      Evaluates environment before annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      AdministrativePreserved mapping before (mapping ++ [before.length + 2])
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload]) ∧
      CallableIndexedSnapshots.All graph.inputs graph.table layout (mapping ++ [before.length + 2])
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue request.payloadType payload])
        (records ++ [⟨before.length, native, ghost, metadata⟩]) := by
  obtain ⟨captured, selected⟩ := Captures.of_slots request.scope request.references slots
  have frame := allocation_frame mapping before (SourceCoreCallableIndexedFrames.encode layout native)
    (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured) (optionalValue request.payloadType payload)
  refine ⟨captured, evaluates allocation annotation same reference read selected payloadAt, frame, ?_⟩
  intro record member
  rcases List.mem_append.mp member with old | fresh
  · exact snapshots.transport frame record old
  · have sameRecord : record = ⟨before.length, native, ghost, metadata⟩ := List.mem_singleton.mp fresh
    subst record
    exact CallableIndexedSnapshots.completed history bounded _ _

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationCompletion
