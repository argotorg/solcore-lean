import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadCompletion
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource

/-! Both directions of accepted ordinary reads preserve the real mixed heap.
Native completion is assembled from the selected cell and literal code; the
independent Source trace is then identified by local read uniqueness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

/-- An actual ordinary read finishes by the emitted optional-cell code. Lazy
mapping initialization writes the original mapped location. -/
theorem Certificate.cell_native_terminates {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) cells)
    {sourceContext : SourceSemantics.Context} (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual) :
    ∃ value finalStore, Evaluates actual store (code.rename ξ) value finalStore := by
  have monomorphic := certificate.monomorphic
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
  obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
    GenericHeap.CellHeapRepresents.lookup_visible environments heaps lookup slot
  have sameCell := read.functional selectedRead
  subst selected
  have absent := locals.descriptor_empty_of_monomorphic heapTyped declaredScope lookup read monomorphic
  have represented := ordinaryCells.project represented absent
  cases represented with
  | initialized payload =>
    cases emitted with
    | ordinary _ =>
      change ∃ value finalStore, Evaluates actual store (OptionalCell.read type (.var (ξ index)) reason) value finalStore
      exact ⟨_, store, OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead⟩
    | mapping declared generated =>
      obtain ⟨_, _, quoted, _⟩ := generated.represents functions extension (.mapping .empty) mapping world
      rw [mapping_rename quoted]
      exact ⟨_, store, SourceCoreCompatibleDataExpressions.readMapping_present (.var (agrees nativeLookup)) nativeRead⟩
  | @uninitialized sourceType _ projected =>
    change sourceType = declared.scheme.body at cellType
    cases emitted with
    | ordinary _ =>
      change ∃ value finalStore, Evaluates actual store (OptionalCell.read type (.var (ξ index)) reason) value finalStore
      exact ⟨_, store, OptionalCell.read_failure reason (.var (agrees nativeLookup)) nativeRead⟩
    | @mapping key value literal declared generated =>
      obtain ⟨native, encodedType, quoted, payload⟩ := generated.represents functions extension (.mapping .empty) mapping world
      have same : encodedType = type := Except.ok.inj (payload.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      rw [mapping_rename quoted]
      refine ⟨.inRight .word native, store.set target (.inRight .unit native),
        SourceCoreCompatibleDataExpressions.readMapping_initializes (.var (agrees nativeLookup)) nativeRead ?_ nativeRead⟩
      rw [quoted.weaken 0]
      rw [quoted.weaken 0]
      exact quoted.evaluates _ _

theorem Certificate.cell_preserves_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) cells)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨value, finalStore, evaluation⟩ := certificate.cell_native_terminates functions extension ordinaryCells
    binding environments heaps heapTyped locals agrees
  obtain ⟨actualOutcome, actualHeap, sourceTrace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.cell_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
      environments heaps heapTyped locals agrees uninitialized evaluation
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have absent := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup read certificate.monomorphic
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read absent sourceTrace trace
  exact ⟨value, finalStore, evaluation, represented, finalHeaps, frame, metadata⟩

theorem Certificate.cell_reflects_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) cells)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.cell_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
    environments heaps heapTyped locals agrees uninitialized evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
