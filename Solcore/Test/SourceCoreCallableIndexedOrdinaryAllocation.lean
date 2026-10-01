import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

/-! A real accepted marked callback allocates an ordinary source cell at the
native payload index, while the snapshot and marker remain administrative.
The source binder retains its raw type. Complete native definitions and source
payload interpretation are explicit rather than inferred from scalar typing. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedOrdinaryAllocation
open Core Frontend SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CallableIndexedOrdinaryAllocation

example {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError) request = .ok code)
    (definitions : layouts.definitions = catalog.definitions)
    (registered : layout.Registered catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {location : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (absent : request.payload = none)
    (projected : projects request.binder.scheme.body request.payloadType) :
    ∃ marker markerType,
      Evaluates actual store code (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inLeft request.payloadType .unit]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, markerType, OptionalCell.cellType request.payloadType])
        ⟨heap.cells ++ [⟨request.binder.scheme.body, none, none⟩]⟩
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inLeft request.payloadType .unit]) ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [layout.type, markerType, OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, ⟨heap.cells.length⟩) :: environment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical) := by
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError accepted
  obtain ⟨captured, evaluated, related, allocatedReference, _⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments agrees heaps
      reference read (.absent absent) (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨_, _, emitted.symm ▸ evaluated, related, bind_environment environments allocatedReference⟩

/-- Captured source cells can themselves hold functions. Capture typing reads
the finite world's cell-reference type and does not unfold a recursive heap. -/
example (catalog : SourceCoreDataCatalog.Catalog) (first second : Resolved.LocalId)
    (inserted : Value) :
    ∃ captured,
      Captures [inserted, .cellRef (OptionalCell.cellType (.function .unit .unit)) 0,
        .cellRef (OptionalCell.cellType (.function .unit .unit)) 0]
        (fun index => index + 1) [(first, .function .unit .unit), (second, .function .unit .unit)] captured ∧
      RuntimeValueHasType [OptionalCell.cellType (.function .unit .unit)] captured
        (.product (OptionalCell.referenceType (.function .unit .unit))
          (OptionalCell.referenceType (.function .unit .unit))) catalog.definitions := by
  have reference : ReferenceRepresents [0] [OptionalCell.cellType (.function .unit .unit)]
      ⟨0⟩ 0 (.function .unit .unit) := ⟨rfl, rfl⟩
  have environments : DataHeap.EnvRepresents catalog [0] [OptionalCell.cellType (.function .unit .unit)] []
      [(first, .function .unit .unit), (second, .function .unit .unit)] [(first, ⟨0⟩), (second, ⟨0⟩)]
      [.cellRef (OptionalCell.cellType (.function .unit .unit)) 0,
        .cellRef (OptionalCell.cellType (.function .unit .unit)) 0] :=
    .cons reference (.cons reference (.nil .nil))
  exact captures_typed environments (fun found => found)

end Solcore.Test.SourceCoreCallableIndexedOrdinaryAllocation
