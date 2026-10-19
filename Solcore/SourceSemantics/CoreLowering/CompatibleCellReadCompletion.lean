import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations

/-! Accepted ordinary reads in mixed heaps. The compiler's actual monomorphic
binder receipt and deep Source heap typing exclude a descriptor only at the
selected location. Other generalized cells keep their original relation. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.Dynamic.EnvironmentAgrees
open Frontend SourceInference TypeSystem

/-- The principal descriptor's genuine polymorphic code rules out its storage
under a monomorphic first-match lexical binding. -/
theorem descriptor_empty_of_monomorphic
    {context : Context} {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : Environment} (agrees : EnvironmentAgrees heap scope environment)
    (heapTyped : HeapWellTyped context heap)
    {id : Resolved.LocalId} {scheme : Scheme} {location : Location} {cell : Cell}
    (staticLookup : Resolved.LocalScope.Lookup scope id scheme)
    (dynamicLookup : Environment.LooksUp environment id location)
    (read : Heap.Reads heap location cell) (monomorphic : scheme.quantified = []) :
    cell.generalized = none := by
  cases stored : cell.generalized with
  | none => rfl
  | some function =>
      obtain ⟨_, sameScheme⟩ := agrees.lookup_generalized staticLookup dynamicLookup read stored
      have member : cell ∈ heap.cells := by
        cases read with
        | intro selected =>
          have membership : ∀ {cells : List Cell} {index : Nat} {selectedCell : Cell},
              Heap.CellAt cells index selectedCell → selectedCell ∈ cells := by
            intro cells index selectedCell atCell
            induction atCell with
            | head => simp
            | tail _ ih => exact List.mem_cons_of_mem _ ih
          exact membership selected
      have code := ((heapTyped cell member).generalized_inv stored).2.code
      exact False.elim (code.polymorphic (sameScheme ▸ monomorphic))

end Solcore.SourceSemantics.Dynamic.EnvironmentAgrees

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

/-- Mapping completion constructs only the actual raw source rule and its full
heap relation; callers choose their ordinary or staged outer constructor. -/
theorem Certificate.cell_mapping_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) cells)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    (declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep}
    {result : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        certificate.node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults (.value sourceValue) result ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
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
  cases emitted with
  | ordinary notMapping => exact False.elim (notMapping declaredMapping)
  | @mapping key value literal declaredType generated =>
    obtain ⟨empty, encodedType, quoted, emptyRep⟩ := generated.represents functions extension (.mapping .empty) mapping world
    rw [mapping_rename quoted] at evaluation
    have completed := read_completed (agrees nativeLookup) nativeRead quoted evaluation
    cases represented with
    | initialized payload =>
      dsimp only at cellType
      rcases completed with ⟨_, _, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
      · cases sameOptional
        subst result finalStore
        exact ⟨_, heap, form ▸ .local rfl lookup read rfl rfl,
          .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
      · cases impossible
    | @uninitialized sourceType _ projected =>
      change sourceType = declared.scheme.body at cellType
      have same : encodedType = type := Except.ok.inj (emptyRep.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      rcases completed with ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, sameValue, originalWritten⟩
      · cases impossible
      · cases sameOptional
        subst result
        obtain ⟨after, written⟩ := writes_exists read (.mapping _ _ [])
        have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping _ _ []) empty type :=
          cellType.symm ▸ emptyRep
        obtain ⟨updated, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized ordinaryCells reference read absent cellPayload written
        have sameStore := Option.some.inj (nativeWritten.symm.trans originalWritten)
        cases sameStore
        exact ⟨_, after, form ▸ .localEmptyMapping rfl lookup read rfl (cellType.trans declaredType) rfl written,
          .value (.compatible (cellType ▸ occurrence) cellPayload), finalHeaps, frame, .of_write written⟩

/-- Every completed accepted local read determines its independent source outcome. -/
theorem Certificate.cell_completed_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
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
  by_cases declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value
  · obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata⟩ :=
      certificate.cell_mapping_completed functions extension ordinaryCells program sourceContext evidence binding declaredMapping
        environments heaps heapTyped locals agrees evaluation
    refine ⟨.value sourceValue, after, .value (.intro (middle := after) (raw := sourceValue) (lookupExpression?_sound certificate.metadata.found) ?_ ?_),
      represented, finalHeaps, frame, metadata⟩
    · simpa only [certificate.metadata.requirements, certificate.metadata.coercions] using raw
    · rw [certificate.metadata.coercions]; exact .nil
  · have monomorphic := certificate.monomorphic
    rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
    rcases binding with ⟨declaredScope, occurrence⟩
    dsimp only at *
    cases emitted with
    | mapping declaredType generated => exact False.elim (declaredMapping ⟨_, _, declaredType⟩)
    | ordinary _ =>
      obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
      obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
        GenericHeap.CellHeapRepresents.lookup_visible environments heaps lookup slot
      have sameCell := read.functional selectedRead
      subst selected
      have absent := locals.descriptor_empty_of_monomorphic heapTyped declaredScope lookup read monomorphic
      have represented := ordinaryCells.project represented absent
      have ordinary := represented.ordinary
      have result := ordinary_completed (agrees nativeLookup) nativeRead evaluation
      have contains := lookupExpression?_sound metadata.found
      cases represented with
      | @initialized sourceType _ sourceValue nativeValue payload =>
        dsimp only at cellType
        rcases result with ⟨_, native, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
        · cases sameOptional
          subst value finalStore
          refine ⟨.value _, heap, .value (.intro (middle := heap) (raw := sourceValue) contains ?_ ?_),
            .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read ordinary rfl
          · rw [metadata.coercions]; exact .nil
        · cases impossible
      | uninitialized projected =>
        dsimp only at cellType
        rcases result with ⟨_, _, impossible, _⟩ | ⟨_, _, _, sameValue, sameStore⟩
        · cases impossible
        · subst value finalStore
          refine ⟨.fault (.uninitializedLocation location), heap, .fault (.form contains ?_),
            .fault (uninitialized location _ ⟨contains, form, declaredScope, occurrence, lookup, read,
              cellType, ordinary, rfl, by simpa only [cellType] using declaredMapping⟩), heaps, .refl _ _, .refl _⟩
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read ordinary rfl (by simpa only [cellType] using declaredMapping)

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Certificate.cell_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
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
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.cell_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
    environments heaps heapTyped locals agrees (fun location _ _ => uninitialized location) evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
