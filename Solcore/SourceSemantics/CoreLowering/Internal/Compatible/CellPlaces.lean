import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.GenericCellHeap
import Solcore.SourceSemantics.CoreLowering.DataMappingComparison
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
import Solcore.SourceSemantics.Dynamic.Initialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality

/-!
# Compatible profile: cell places

Places, bare writes, bit-not updates, mapping helpers and index lookups over cells.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellReadCompletion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentSnapshot
/-! A writable monomorphic root selects an ordinary cell in the actual mixed
heap. The snapshot and native getter retain the existing transaction layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {registry : SourceCoreRawMetadata.Registry}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment}
  {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {index : Nat}

/-- Resolve the real lexical reference, then select its optional snapshot.
The source heap, native store, and location map are unchanged. -/
theorem snapshot_of_cell_heap {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context} {scope : Scope} {administrativeContext : Core.Context}
    {canonical : Environment} {ξ : Renaming}
    (layout : Layout compilation prepared) (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType) :
    ∃ snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index),
      snapshot.cell.generalized = none := by
  classical
  obtain ⟨scheme, schemeLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
  have nativeLookup := agrees nativeLookup
  obtain ⟨actualCell, optional, payload, actualRead, payloadType, nativeRead, represented⟩ :=
    heaps.cells reference.mapped
  have sameCell := read.functional actualRead
  subst actualCell
  have samePayload : payload = prepared.route.rootType := by
    simpa [OptionalCell.cellType] using Option.some.inj (payloadType.symm.trans reference.typed)
  subst payload
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped schemeLookup lookup read monomorphic
  have represented := ordinaryCells.project represented ordinary
  cases represented with
  | uninitialized projected =>
    by_cases isMapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
    · obtain ⟨key, value, declared⟩ := isMapping
      have sourceType := cellType.trans declared
      simp only at sourceType
      obtain ⟨native, root⟩ := CompatiblePlaceLiveRoot.RootRead.virtual (layout.virtual key value declared)
        extension (sourceType ▸ projected) (sourceType ▸ read) reference nativeRead
      exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        (sourceType.symm ▸ root.input.initial), .present (declared.symm ▸ root.payload), root.input.normalize _ store _ (.first (.var rfl))⟩, rfl⟩
    · have noVirtual := layout.ordinary (fun key value same => isMapping ⟨key, value, same⟩)
      refine ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        .uninitialized ?_, .absent, ?_⟩, rfl⟩
      · rintro ⟨key, value, same⟩
        exact isMapping ⟨key, value, cellType.symm.trans same⟩
      · simpa only [normalizeRoot, noVirtual] using
          (Evaluates.first (Evaluates.var (index := 0) rfl) :
            Evaluates (.pair (.inLeft prepared.route.rootType .unit) .unit :: keysEnvironment prepared.route.rootType target .unit actual)
              store (.first (.var 0)) (.inLeft prepared.route.rootType .unit) store)
  | initialized related =>
    have root := CompatiblePlaceLiveRoot.RootRead.initialized read reference nativeRead related
    exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
      .initialized, .present (cellType ▸ related), root.input.normalize _ store _ (.first (.var rfl))⟩, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentRhs
/-! A completed RHS retains the original snapshot and reads the same ordinary
root from its actual later mixed heap. Descriptor retention is an executed
child effect, never a compiler premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

structure CellRhsResult (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend heap after
  effect : CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld after finalStore
  latest : Nonempty (CompatiblePlaceRhs.Latest checked registry functions finalMap finalWorld prepared snapshot.resolved snapshot.target after finalStore)

theorem latest_of_cell_heap
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (ordinary : snapshot.cell.generalized = none) {nextMap : LocationMap} {nextWorld : StoreTyping} {after : Dynamic.Heap} {finalStore : Store}
    (heaps : GenericHeap.CellHeapRepresents cells nextMap nextWorld after finalStore)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Nonempty (CompatiblePlaceRhs.Latest checked registry functions nextMap nextWorld prepared snapshot.resolved snapshot.target after finalStore) := by
  obtain ⟨cell, read, sameType, sameDescriptor⟩ := metadata _ _ snapshot.read
  have reference := snapshot.reference.extend maps worlds
  obtain ⟨selected, optional, payload, selectedRead, payloadType, nativeRead, represented⟩ :=
    heaps.cells reference.mapped
  have sameCell := read.functional selectedRead
  subst selected
  have samePayload : payload = prepared.route.rootType := by
    simpa [OptionalCell.cellType] using Option.some.inj (payloadType.symm.trans reference.typed)
  subst payload
  have represented := ordinaryCells.project represented (sameDescriptor.trans ordinary)
  exact ⟨⟨cell, optional, read, sameType.trans snapshot.type, reference, nativeRead, represented⟩⟩

/-- Package a completed child and derive its latest ordinary root from the
actual heap metadata extension. -/
theorem cell_rhs_of_expression
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (ordinary : snapshot.cell.generalized = none)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {value : Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after)
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore)
    (represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value)
    (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (effect : CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld after finalStore) :
    CellRhsResult (cells := cells) (instances := instances) (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot
      outcome after value finalStore finalMap finalWorld :=
  ⟨trace, evaluated, represented, heaps, maps, worlds, frame, metadata, effect,
    latest_of_cell_heap snapshot ordinaryCells ordinary heaps maps worlds metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentCommit
/-! The final setter writes the post-RHS ordinary root while using the saved
pre-RHS snapshot for the modifier. Actual descriptor rows retain their source
metadata and native values through the completed write. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {registry : SourceCoreRawMetadata.Registry}
  {mapping : LocationMap} {world : StoreTyping}

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- A successful RHS and modifier produce an exact whole-prefix agreement,
including typed seven slots for the real renamed continuation. -/
theorem cell_commit_with_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (bare : place.projections = [])
    {right updated : Dynamic.Value} {rightValue updatedValue : Value} {rhsHeap : Dynamic.Heap}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {operator : Syntax.ValueAssignOp} {invalid : Word}
    (rhs : CellRhsResult (cells := cells) (instances := instances) (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot (.value right) rhsHeap
        (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType)
    (replacement : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
    (applied : Dynamic.AssignmentValueApplies operator snapshot.initial right updated)
    (modified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
      (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
      (.inRight .word updatedValue) rhsStore)
    {actualContext : Core.Context} (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ after finalStore,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment heap place id updated after ∧
      Dynamic.Heap.Writes rhsHeap snapshot.location (some updated) after ∧
      GenericHeap.CellHeapRepresents cells rhsMap rhsWorld after finalStore ∧
      AdministrativePreserved mapping store rhsMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      RuntimeEnvironmentHasTypes rhsWorld
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        (writtenContext prepared actualContext) ambient.definitions ∧
      AdministrativePreserved rhsMap rhsStore rhsMap finalStore ∧
      Dynamic.HeapMetadataExtend rhsHeap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store rhsMap rhsWorld after finalStore ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨latest⟩ := rhs.latest
  obtain ⟨initial, initialValue⟩ := cell_initial latest.related
  have written := DataPlaceCommitReflection.source_writes latest.read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    rhs.heaps.write_initialized ordinaryCells latest.reference latest.read latest.related.ordinary
      (latest.type.symm ▸ replacement) written
  have writeEffect : CellAwareScopeAuthority.Effect instances rhsMap rhsWorld rhsHeap rhsStore rhsMap rhsWorld
      ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ finalStore :=
    .write_ordinary rhs.heaps.injective latest.read latest.related.ordinary latest.reference written coreWritten
  have trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment heap place id updated
        ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ := by
    cases rhs.trace with
    | value right =>
      exact .intro (snapshot.resolves bare) right
        (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written)
  refine ⟨_, finalStore, trace, written, finalHeaps, rhs.frame.trans writeFrame, rhs.metadata.trans (.of_write written), ?_, writeFrame, .of_write written, rhs.effect.trans writeEffect, ?_⟩
  · exact .cons .unit (.cons replacement.runtime_hasType (.cons replacement.runtime_hasType
      (.cons rightRep.runtime_hasType (.cons (snapshot.represented.extend rhs.maps rhs.worlds).runtime_hasType
        (.cons .unit (.cons (.cellRef latest.reference.typed) (actualTyped.weaken rhs.worlds)))))))
  · intro next outputType
    exact (snapshot_prefix layout snapshot _ _ _ _ _).trans
      ((ContinuationAgreement.bind rhs.evaluated).trans
        ((ContinuationAgreement.bind modified).trans
          ((ContinuationAgreement.bind (setter_evaluates layout snapshot.value rightValue updatedValue latest.nativeRead)).trans
            (ContinuationAgreement.letE (.storeCell (.var rfl) latest.nativeRead (.inRight (.var rfl)) coreWritten)))))
end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBareBitNotPrefix
/-! A numeric bare snapshot creates a real mapped commit and an exact typed
seven-slot continuation in the actual renamed environment. Its Unit RHS has
no source child. Every native phase is constructed from a represented live cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {location : Dynamic.Location} {target : Location} {sourceValue : Dynamic.Value} {value : Value}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {actual : Environment} {actualContext : Core.Context} {index : Nat} {ξ : Renaming}

/-! The actual six phases and write expose a strict child of the original
Core derivation. Source updates have no expression child; continuation
agreement transports results but supplies no execution-size bound. -/
theorem initialized_prefix_cells_sized (layout : Layout prepared)

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (nativeRead : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ updated replacement after finalStore slots,
      Dynamic.BitNotSnapshot (some sourceValue) updated ∧
      Dynamic.Heap.Writes heap location (some updated) after ∧
      ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      (∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ))) ∧
      ∀ {next : Expr} {output : Ty} {result : Value} {after : Store} {size : Nat},
        CoreProof.EvaluationSize size actual store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
            next output operator true invalid).rename ξ) result after →
        ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (slots ++ actual)
          finalStore (shift 7 (next.rename ξ)) result after := by
  obtain ⟨updated, replacement, related, applies, modified, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.success profile represented
      (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      (snapshot := .var 1) (rhs := .var 0) (.var rfl) operator store invalid
  have written := DataPlaceCommitReflection.source_writes read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized ordinaryCells reference read rfl related written
  have writeEffect : CellAwareScopeAuthority.Effect instances mapping world heap store mapping world
      ⟨heap.cells.set location.index ⟨prepared.route.rootSourceType, some updated, none⟩⟩ finalStore :=
    .write_ordinary heaps.injective read rfl reference written coreWritten
  let slots : Environment := [.unit, replacement, replacement, .unit, .inRight .unit value, .unit,
    .cellRef (OptionalCell.cellType prepared.route.rootType) target]
  have rhs : Evaluates (snapshotEnvironment prepared.route.rootType target .unit (.inRight .unit value) actual)
      store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
    exact .inRight .unit
  have modifier : Evaluates (rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit actual)
      store (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
      (.inRight .word replacement) store := by simpa only [← layout.sameType] using modified
  have agreement : ∀ next output, ContinuationAgreement actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ)
      (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
    intro next output
    rw [execute_rename layout]
    exact (ContinuationAgreement.letE (.var lookup)).trans
      ((ContinuationAgreement.bind (CompatibleBareBitNotNative.keys_evaluates _ _)).trans
        ((ContinuationAgreement.bind (CompatibleBareBitNotNative.getter_evaluates layout nativeRead)).trans
          ((ContinuationAgreement.bind rhs).trans
            ((ContinuationAgreement.bind modifier).trans
              ((ContinuationAgreement.bind (CompatibleBareBitNotNative.setter_evaluates layout
                (.inRight .unit value) replacement nativeRead)).trans
                (ContinuationAgreement.letE (.storeCell (.var rfl) nativeRead (.inRight (.var rfl)) coreWritten)))))))

  refine ⟨updated, replacement, _, finalStore, slots, applies, written, related, finalHeaps, frame,
    .of_write written, writeEffect, rfl, ?_, agreement, ?_⟩
  ·
    exact .cons .unit (.cons related.runtime_hasType (.cons related.runtime_hasType
      (.cons .unit (.cons (.inRight represented.runtime_hasType) (.cons .unit (.cons (.cellRef reference.typed) actualTyped))))))
  · intro next output result after size completed
    have terminal := (agreement .unit output).wrap
      (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
        (Evaluates.unit (environment := slots ++ actual) (store := finalStore)))
    rw [execute_rename layout] at terminal completed
    exact RecursiveNamedBareAssignmentContracts.execute_continuation_sized
      (.var lookup) (CompatibleBareBitNotNative.keys_evaluates _ _)
      (CompatibleBareBitNotNative.getter_evaluates layout nativeRead) rhs modifier
      (CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) replacement nativeRead)
      terminal completed

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBareBitNotSource
/-! Independent bare unary source updates and completed actual renamed Core
code agree. Successful reflection returns all seven typed slots, with a Unit
RHS; preservation uses the exact source write and supports any continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open CompatibleRenamedBareBitNot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap)
    (world : StoreTyping) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason before)
      (result : value = .inLeft output (.word token)) (represented : faults reason token)
      (storeEq : finalStore = store) :
      Result checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore
  | success {updated : Dynamic.Value} {replacement : Value} {after : Dynamic.Heap}
      {written : Store} {slots : Environment}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType)
      (heaps : GenericHeap.CellHeapRepresents cells mapping world after written)
      (frame : AdministrativePreserved mapping store mapping written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store mapping world after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (continuation : Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :
      Result checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap)
    (world : StoreTyping) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word}
      (trace : SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source environment before place reason before)
      (result : value = .inLeft output (.word token)) (represented : faults reason token)
      (storeEq : finalStore = store) :
      ResultAt size checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {replacement : Value} {after : Dynamic.Heap}
      {written : Store} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType)
      (heaps : GenericHeap.CellHeapRepresents cells mapping world after written)
      (frame : AdministrativePreserved mapping store mapping written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store mapping world after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :
      ResultAt size checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {prepared : Prepared} {place : PlaceResolution} {scope : Scope}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}


/-- Erasing sizes preserves the independent source outcome and actual seven slots. -/
theorem ResultAt.erase {size : Nat} {faults : FaultRep} {next : Expr} {output : Ty}
    {result : Value} {finalStore : Store}
    (receipt : ResultAt size compilation.checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place
      environment before store mapping world actual actualContext ξ next output result finalStore) :
    Result compilation.checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place
      environment before store mapping world actual actualContext ξ next output result finalStore := by
  cases receipt with
  | fault trace same represented stores => exact .fault trace.sound same represented stores
  | success trace represented heaps frame metadata effect count typed _ continuation =>
    exact .success trace.sound represented heaps frame metadata effect count typed continuation.sound

private theorem read_at_cells
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {location : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads before location cell) (ordinary : cell.generalized = none) :
    ∃ value, store.read? target = some value ∧
      GenericHeap.CellRepresents (payloadModel compilation.checked registry functions) mapping world cell value type := by
  obtain ⟨actual, value, payload, sourceRead, typed, native, represented⟩ := heaps.cells reference.mapped
  have same := sourceRead.functional read
  subst actual
  have samePayload : payload = type := by
    simpa [OptionalCell.cellType] using Option.some.inj (typed.symm.trans reference.typed)
  subst payload
  exact ⟨value, native, ordinaryCells.project represented ordinary⟩

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

theorem preserves_prefix (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after) (operator : Option BinaryOp) (invalid : Word) :
    ∃ replacement finalStore slots,
      ValueRep compilation.checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  cases trace with
  | intro resolve written =>
    cases resolve with
    | @intro _ _ _ _ _ _ _ location initialCell currentCell resolved initial selected lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases written with
      | intro writeRead typeEq writeInitial changed sourceWrite =>
        cases changed with
        | leaf applies =>
          obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
          have sameLocation := lookup.functional staticLookup
          subst staticLocation
          have sameCell := currentRead.functional staticRead
          subst staticCell
          have cellType := staticType.trans bodyEq
          obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
          cases root with
          | emptyMapping key value =>
            have impossible := cellType ▸ profile
            rcases impossible with impossible | impossible <;> cases impossible
          | uninitialized => cases applies
          | initialized =>
            obtain ⟨optional, nativeRead, represented⟩ := read_at_cells ordinaryCells heaps reference currentRead rfl
            cases represented with
            | @initialized rawType payload sourceValue nativeValue related =>
              simp only at cellType
              subst_vars
              obtain ⟨replacement, native, generatedAfter, finalStore, slots, generated, generatedWrite,
                related, finalHeaps, frame, metadata, effect, count, typed, agreement, _⟩ :=
                initialized_prefix_cells_sized layout profile ordinaryCells heaps reference currentRead nativeRead related
                  (agrees nativeLookup) actualTyped operator invalid
              have same := CompatiblePlaceBitNotModifier.functional generated applies
              subst replacement
              have same := writes_functional generatedWrite sourceWrite
              subst generatedAfter
              exact ⟨native, finalStore, slots, related, finalHeaps, frame, metadata, effect, count, typed, agreement⟩

/-- The sole runtime premise is completion of the real renamed code. It
produces an independent source fault/write and the actual typed continuation. -/
theorem reflects_sized (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {faults : FaultRep} {next : Expr} {output : Ty} {operator : Option BinaryOp} {invalid : Word}
    {result : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result finalStore) :
    ResultAt size compilation.checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
      mapping world actual actualContext ξ next output result finalStore := by
  obtain ⟨scheme, schemeLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, cell, sourceLookup, sourceRead, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped schemeLookup sourceLookup sourceRead monomorphic
  obtain ⟨optional, nativeRead, represented⟩ := read_at_cells ordinaryCells heaps reference sourceRead ordinary
  cases represented with
  | uninitialized projected =>
    have initial : Dynamic.RootInitialValue _ none := .uninitialized (by
      rintro ⟨key, value, same⟩
      have impossible : prepared.route.rootSourceType = .mapping key value := cellType.symm.trans same
      rw [impossible] at profile
      rcases profile with impossible | impossible <;> cases impossible)
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead initial
    obtain ⟨resultEq, storeEq⟩ := absent_reflects layout (agrees nativeLookup) nativeRead completed.sound
    obtain ⟨sourceSize, sourceTrace⟩ := SourceExecutionSize.SourcePlaceBitNotFaults.has_size (.uninitialized trace rfl)
    exact .fault sourceTrace resultEq token storeEq
  | @initialized type _payload sourceValue value related =>
    simp only at cellType
    subst type
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead Dynamic.RootInitialValue.initialized
    obtain ⟨updated, replacement, after, written, slots, applies, sourceWrite, represented, finalHeaps,
      frame, metadata, effect, count, typed, _agreement, remaining⟩ := initialized_prefix_cells_sized layout profile ordinaryCells heaps
        reference sourceRead nativeRead related (agrees nativeLookup) actualTyped operator invalid
    obtain ⟨sourceSize, sourceTrace⟩ := SourceExecutionSize.SourcePlaceSnapshotUpdate.has_size
      (.intro trace (.intro sourceRead rfl .initialized (.leaf applies) sourceWrite))
    obtain ⟨remainingSize, smaller, continuation⟩ := remaining completed
    exact .success sourceTrace represented finalHeaps frame metadata effect count typed smaller continuation

theorem reflects (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {faults : FaultRep} {next : Expr} {output : Ty} {operator : Option BinaryOp} {invalid : Word}
    {result : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result finalStore) :
    Result compilation.checked registry functions (cells := cells) (instances := instances) program context evidence source faults prepared place environment before store
      mapping world actual actualContext ξ next output result finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  exact (reflects_sized layout bare profile environments ordinaryCells heaps heapTyped locals agrees actualTyped slot rootTyped token sized).erase

private theorem excludes_target_fault {heap after : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {reason : Dynamic.SemanticFault}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment heap place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling found missing => exact missing.excludes_read (found.functional lookup ▸ read)
  | projectionExpression found initialRead fault => rw [bare] at fault; cases fault
  | danglingAfterProjections found initialRead keys missing =>
    rw [bare] at keys
    cases keys
    exact missing.excludes_read initialRead
  | projectionRead found initialRead keys currentRead root fault =>
    rw [bare] at keys
    cases keys
    cases fault
  | uninitialized found initialRead keys currentRead empty notMapping nonempty =>
    rw [bare] at keys
    cases keys
    exact nonempty rfl

/-- Every independent fault of a live numeric bare root is the absent unary
operand. Generated helpers and the continuation do not alter either heap. -/
theorem preserves_fault (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (next : Expr) (output : Ty) (operator : Option BinaryOp) (invalid : Word) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ) (.inLeft output (.word invalid)) store := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
  cases trace with
  | target fault => exact (excludes_target_fault bare staticLookup staticRead fault).elim
  | uninitialized resolve empty =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases empty
      cases root with
      | uninitialized notMapping =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := read_at_cells ordinaryCells heaps reference currentRead rfl
        cases represented with
        | uninitialized projected => exact ⟨rfl, rfl,
            absent_evaluates layout (agrees nativeLookup) nativeRead next output operator invalid⟩
  | operand resolve selected invalidOperand =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases selected
      have sameLocation := lookup.functional staticLookup
      subst staticLocation
      have sameCell := currentRead.functional staticRead
      subst staticCell
      have cellType := staticType.trans bodyEq
      cases root with
      | emptyMapping key value =>
        have impossible := cellType ▸ profile
        rcases impossible with impossible | impossible <;> cases impossible
      | initialized =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := read_at_cells ordinaryCells heaps reference currentRead rfl
        cases represented with
        | initialized related =>
          have profile := cellType ▸ profile
          obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceNumericBitNotModifier.success profile related
            (environment := [_]) (rhs := .unit) (.var (index := 0) rfl) operator store invalid
          exact (valid invalidOperand).elim

end Solcore.SourceSemantics.CoreLowering.CompatibleCellRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellBitNotStatementMeaning
/-! Bare unary head semantics close the actual numeric update/fault and retain
all seven real administrative values. The RHS slot is Unit, not a source child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel values.checked registry functions) cells)
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include ordinaryCells environments heaps locals agrees actualTyped in
theorem preserves_prefix_cells {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨_, finalStore, slots, _, finalHeaps, frame, metadata, effect, count, typed, continuation⟩ :=
    CompatibleCellRenamedBareBitNot.preserves_prefix (compilation := values) head.layout head.bare head.profile
      environments ordinaryCells heaps locals agrees actualTyped head.slot head.writable trace (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
  exact ⟨finalStore, mapping, world, slots, finalHeaps, .refl _, .refl _, frame, metadata, effect, count, typed, continuation⟩

include ordinaryCells environments heaps locals agrees in
theorem preserves_fault_cells (errors : head.Errors faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨rfl, rfl, evaluated⟩ := CompatibleCellRenamedBareBitNot.preserves_fault (compilation := values)
    head.layout head.bare head.profile environments ordinaryCells heaps locals agrees head.slot head.writable trace
      next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
  exact ⟨head.invalid, store, mapping, world, evaluated, errors, heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _⟩

include ordinaryCells environments heaps locals agrees actualTyped in
theorem reflects_cells_sized (heapTyped : Dynamic.HeapWellTyped context before) (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ sourceSize reason token after finalMap finalWorld,
      SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source environment before assignment.target reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore) ∨
    (∃ sourceSize updated after written finalMap finalWorld slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after written ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < size ∧ EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases CompatibleCellRenamedBareBitNot.reflects_sized (compilation := values) head.layout head.bare head.profile
    environments ordinaryCells heaps heapTyped locals agrees actualTyped head.slot head.writable errors completed with
  | fault trace same matched stores =>
    subst finalStore
    exact .inl ⟨_, _, _, before, mapping, world, trace, same, matched, heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _⟩
  | success trace _ finalHeaps frame metadata effect count typed smaller continuation =>
    exact .inr ⟨_, _, _, _, mapping, world, _, _, trace, finalHeaps, .refl _, .refl _, frame, metadata, effect, count, typed, smaller, continuation⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellReadMeaning
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceCommitReflection
/-! The final mapped write for the projection-parametric shared heap.
This reuses the source write relation; compatibility changes the payload model,
not the store operation, location map, or administrative frame invariant. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceCommitReflection
open Core Frontend SourceInference GeneralHeap DataEquality

/-- Any completed actual storeCell commits precisely the reconstructed source
root once. The mapped heap and old administrative cells are preserved at the
same world; helper allocations have already been reflected before this step. -/
theorem reflects_storeCell {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {cells : GenericHeap.CellModel definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {type : Ty}
    {sourceValue : Dynamic.Value} {value result : Value}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none)
    (represented : model.Represents mapping world cell.type sourceValue value type)
    {environment : Environment} {referenceExpression valueExpression : Expr}
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType type) target))
    (valueSelected : Selects environment valueExpression value)
    (completed : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) result finalStore) :
    ∃ after, result = .unit ∧ Dynamic.Heap.Writes heap location (some sourceValue) after ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧
      finalStore.read? target = some (.inRight .unit value) ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  have written := DataPlaceCommitReflection.source_writes read sourceValue
  obtain ⟨updated, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized ordinaryCells reference read ordinary represented written
  obtain ⟨_, optional, _, _, _, coreRead, _⟩ := heaps.cells reference.mapped
  have actual : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) .unit updated :=
    .storeCell (referenceSelected.evaluates store) coreRead (.inRight (valueSelected.evaluates store)) coreWritten
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed actual
  exact ⟨_, rfl, written, finalHeaps, frame, .of_write written, Store.write?_reads_written coreWritten,
    CellAwareScopeAuthority.Effect.write_ordinary heaps.injective read ordinary reference written coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceCommitReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellMappingHeap
/-! Actual mapping helpers append native administrative cells while retaining
every ordinary and generalized source cell in the same mixed relation.
Runtime typing supplies the extended world, including cyclic closures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellMappingHeap
open Core Frontend GeneralHeap GenericHeap

theorem heap_append {definitions : DataEnvironment} {model : CellModel definitions}
    {mapping : LocationMap} {world futureWorld : StoreTyping} {heap : Dynamic.Heap} {store suffix : Store}
    (related : CellHeapRepresents model mapping world heap store)
    (extension : WorldExtends world futureWorld)
    (typed : RuntimeStoreHasTypes futureWorld (store ++ suffix) definitions) :
    CellHeapRepresents model mapping futureWorld heap (store ++ suffix) := by
  refine ⟨related.length_eq, related.injective, typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, payload, sourceRead, typeRead, coreRead, represented⟩ := related.cells mapped
  exact ⟨cell, value, payload, sourceRead, extension.lookup typeRead,
    by simpa [Store.read?, List.getElem?_append_left (related.target_lt mapped)] using coreRead,
    model.extend represented (.refl _) extension⟩

theorem administrative_append (mapping : LocationMap) (store suffix : Store) :
    AdministrativePreserved mapping store mapping (store ++ suffix) := by
  intro location absent bound
  exact ⟨absent, by simp [Store.read?, List.getElem?_append_left bound]⟩

/-- Combine a proved finite helper evaluation and its exact store suffix with
the actual Core typing proof. The source heap and map remain unchanged. -/
theorem evaluation_preserves_frame {definitions : DataEnvironment} {model : CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    (related : CellHeapRepresents model mapping world heap store)
    {environment : Environment} {context : Core.Context} {expression : Expr} {value : Value} {type : Ty}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (expressionTyped : HasType context expression type definitions)
    (evaluated : Evaluates environment store expression value finalStore)
    {suffix : Store} (extended : finalStore = store ++ suffix) :
    ∃ futureWorld, WorldExtends world futureWorld ∧ CellHeapRepresents model mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld value type definitions ∧
      AdministrativePreserved mapping store mapping finalStore := by
  subst finalStore
  obtain ⟨futureWorld, extension, storeTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluated expressionTyped environmentTyped related.runtime_hasTypes
  exact ⟨futureWorld, extension, heap_append related extension storeTyped, valueTyped,
    administrative_append mapping store suffix⟩

end Solcore.SourceSemantics.CoreLowering.CellMappingHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellIndexLookup
/-! The actual general-key comparator retains mixed ordinary and generalized
cells. Only its native administrative suffix is appended. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives
open CompatibleGeneralIndex

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {cells : GenericHeap.CellModel ambient.definitions}

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) : HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- Comparator closure allocations preserve the source heap and every existing
administrative cell. The captured actual slots must all be typed. -/
theorem lookup_preserves_heap (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {layout : Core.OrderedMapping.Layout} (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (missingBase : Word) :
    ∃ result finalStore futureWorld suffix,
      ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates (key :: Transport.carrier header fallback layout entries :: environment) store
        (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0)) result finalStore ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      finalStore = store ++ suffix := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared faithful functionLeaves keyType fields keyRep
    (key :: Transport.carrier header fallback layout entries :: environment) store missingBase (.var 1) (.var 0) (.var rfl) (.var rfl)
  have nativeTyped := fields.represents.runtime_hasType
  have actualTyped := RuntimeEnvironmentHasTypes.cons keyRep.runtime_hasType (.cons nativeTyped environmentTyped)
  have helperTyped : HasType (layout.keyType :: SourceCoreMappingWithDefault.type layout :: context)
      (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) ambient.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType missingBase (fields.registered.extend_definitions ambient.basePrefix)
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType, SourceCoreDataEquality.comparatorType, keyType] using closed_hasType (prepared.typed.extend_definitions ambient.basePrefix) _
    · exact .var rfl
    · exact .var rfl
  obtain ⟨suffix, appended, _⟩ := Transport.lookupStore_extension prepared layout
    (key :: Transport.carrier header fallback layout entries :: environment) store header fallback entries key
  obtain ⟨futureWorld, extension, futureHeaps, resultTyped, unchanged⟩ :=
    CellMappingHeap.evaluation_preserves_frame heaps actualTyped helperTyped evaluated appended
  exact ⟨result, _, futureWorld, suffix, CompatibleExpressionIndices.extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellIndexTerminal
/-! General index decisions retain the source mapping metadata. Callable type
views and identity observations are supplied by the function model, independently
of native type projection. No extra Core instruction is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionIndices

/-- The final helper creates a source decision and typed administrative suffix.
The key guard follows retained raw types and the authenticated function model. -/
theorem finish_with_diagnostics {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    {cells : GenericHeap.CellModel ambient.definitions}
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue reason faults) :
    ∃ outcome result finalStore futureWorld suffix,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      finalStore = store ++ suffix ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  obtain ⟨rawKey, rawValue, sources, rfl⟩ := source_mapping baseRep (by rw [sourceType]; rfl)
  obtain ⟨tag, nativeEntries, fallback, rfl, keyView, valueView, fields⟩ := header.mapping_fields sourceType baseRep
  have keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey := by
    cases keyRep.source_runtimeView functionTypes with
    | intro typed view =>
      exact .intro typed (view.trans (by simpa only [runtimeType_agrees_metadata] using keyView))
  have nativeKey : Payload registry functions mapping world rawKey layout.keyType keySource keyValue :=
    .compatible keyView.symm (header.keyType ▸ keyRep)
  obtain ⟨result, finalStore, futureWorld, suffix, resultMeaning, evaluated, finalHeaps, worlds, frame, appended⟩ :=
    lookup_preserves_heap comparison faithful functionLeaves header.comparisonType fields nativeKey environmentTyped heaps reason
  have outcome : ∃ outcome, Terminal (.mapping rawKey rawValue sources) keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result := by
    cases resultMeaning with
    | found located represented => exact ⟨_, .found rfl located, .value (.compatible valueView represented)⟩
    | default absent defaulted represented => exact ⟨_, .default rfl absent defaulted, .value (.compatible valueView represented)⟩
    | missing absent unavailable => exact ⟨_, .unavailable rfl keyTyped absent unavailable, .fault (missing rawKey rawValue sources tag nativeEntries fallback
        ⟨lookupExpression?_sound header.metadata.found, lookupExpression?_sound header.baseMetadata.found,
          sourceType, rfl, rfl, keyView, valueView, fields, keyTyped, absent, unavailable⟩)⟩
  obtain ⟨outcome, terminal, represented⟩ := outcome
  exact ⟨outcome, result, finalStore, futureWorld, suffix, terminal, represented, evaluated, finalHeaps, worlds, frame, appended,
    fun _ other => other.functional keyTyped terminal⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
/-! Only the selected writable root is ordinary. Getter and setter helpers
retain all other cells, including captured generalized descriptors. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot CompatibleHeap

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

include ordinaryCells in
/-- Recover the exact optional payload at an existing represented reference.
Native world lookup equates payload types; source cell identity comes from the
independent heap read, never from native type equality. -/
theorem read_at {location : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none) :
    ∃ value, store.read? target = some value ∧
      GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type := by
  obtain ⟨actual, value, payload, sourceRead, typed, native, represented⟩ := heaps.cells reference.mapped
  have same := sourceRead.functional read
  subst actual
  have samePayload : payload = type := by
    simpa [OptionalCell.cellType] using Option.some.inj (typed.symm.trans reference.typed)
  subst payload
  exact ⟨value, native, ordinaryCells.project represented ordinary⟩

include ordinaryCells in
/-- Live initialized-root facts are consequences of the common heap relation. -/
theorem initialized_root {prepared : Prepared} {sourceType : TypeSystem.Ty}
    {location : Dynamic.Location} {target : Location} {sourceRoot : Dynamic.Value}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ value, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit value) sourceRoot value := by
  obtain ⟨optional, native, represented⟩ := read_at ordinaryCells heaps reference read rfl
  cases represented with
  | initialized related => exact ⟨_, read, reference, native, .initialized, related⟩

/-- The declared mapping remains absent on both heaps while the actual
compiler's encoded empty/default value is supplied to the structural getter. -/
theorem virtual_root {context : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {prepared : Prepared}
    {key valueType : TypeSystem.Ty} {location : Dynamic.Location} {target : Location}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel context.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : CompatibleMapping.VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨optional, native, represented⟩ := read_at ordinaryCells heaps reference read rfl
  cases represented with
  | uninitialized projection => exact RootRead.virtual generated extension projection read reference native


/-- The independent Source initial-root receipt selects the actual heap payload. -/
theorem root_of_initial {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {sourceRoot : Dynamic.Value}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (initial : Dynamic.RootInitialValue cell (some sourceRoot))
    (virtual : ∀ key value, cell.type = .mapping key value → CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry) :
    ∃ optional rootValue, RootRead compilation.checked registry functions mapping world prepared heap store
      location target cell optional sourceRoot rootValue := by
  cases cell with
  | mk type value descriptor =>
   cases ordinary
   cases initial with
   | initialized =>
    obtain ⟨value, root⟩ := initialized_root ordinaryCells heaps reference read
    exact ⟨_, value, root⟩
   | emptyMapping key value =>
    obtain ⟨native, root⟩ := virtual_root ordinaryCells heaps reference read
      (virtual key value rfl) extension
    exact ⟨_, native, root⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
/-! Effectful key evaluation and the actual compatible live getter implement
target resolution before the RHS starts. The common heap is transported over
the getter's real administrative allocations; virtual mapping roots remain
uninitialized. No child or helper execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot

/-- The source selected value and exact key/snapshot native runs are outputs
of resolution. The source heap is unchanged by snapshot helper allocation. -/
structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (sourceTarget : Dynamic.ResolvedPlace)
    (environment : Environment) (initialStore : Store) (initialMap : LocationMap)
    (initialWorld : StoreTyping) (before after : Dynamic.Heap) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  selected : Dynamic.Value
  snapshot : Value
  keyStore : Store
  store : Store
  mapping : LocationMap
  world : StoreTyping
  selectedEq : sourceTarget.selected = some selected
  currentCell : Dynamic.Cell
  currentRead : Dynamic.Heap.Reads after sourceTarget.location currentCell
  ordinary : currentCell.generalized = none
  currentType : currentCell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  shaped : DataPlaceKeyOrder.Values place.projections sources sourceTarget.projections
  keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target environment) initialStore
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) environment) keyStore
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (.inRight .word (.inRight .unit snapshot)) store
  keysRelated : DataExpressionSequence.Values (payloadModel checked registry functions) mapping world
    sourceTypes (codes.map (·.type)) sources values
  snapshotRelated : ValueRep checked registry functions mapping world leaf selected snapshot prepared.route.leafType
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances initialMap initialWorld before initialStore mapping world after store


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
/-! RHS execution uses the previously selected snapshot but returns the live
root in the post-RHS heap. Both directions instantiate the universal expression
IH under execute's real three hidden slots. None of the fields below is an
input to a compiler certificate; they are semantic output witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceRhs (Latest)

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}

variable (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Snapshot, keys, and RHS all retain their own source/native identities.
The latest-root receipt refers to the new heap, not the saved snapshot heap. -/
structure Result (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (environment : Dynamic.Environment) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (store : Store) (mapping : LocationMap) (world : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after
  evaluated : Evaluates
    (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
    resolution.store (shift 3 lowered.expression) value store
  represented : ResultRepresents (payloadModel checked registry functions) mapping world node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  effect : CellAwareScopeAuthority.Effect instances resolution.mapping resolution.world targetHeap resolution.store mapping world after store
  latest : Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store)

theorem latest_of_heap
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells) {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, sameDescriptor⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells heaps reference read (sameDescriptor.trans resolution.ordinary)
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {environment : Dynamic.Environment} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- RHS effects preserve the previous snapshot as a related value. It is not
replaced by the value obtained when the root is read again for writeback. -/
theorem Result.saved_snapshot {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world) :
    ValueRep checked registry functions mapping world leaf resolution.selected resolution.snapshot prepared.route.leafType :=
  resolution.snapshotRelated.extend (.refl _) result.maps result.worlds

/-- A successful source RHS cannot turn an initialized root into an absent
one. This fact comes from the independent trace, not the heap metadata law. -/
theorem Result.initialized {right : Dynamic.Value} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment (.value right) after value store mapping world)
    (wasInitialized : resolution.currentCell.value ≠ none)
    (latest : Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) :
    latest.cell.value ≠ none := by
  cases result.trace with
  | value trace =>
    obtain ⟨cell, read, initialized⟩ := trace.initialization_extends _ _ resolution.currentRead wasInitialized
    exact latest.read.functional read ▸ initialized

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhsReflection
/-! The actual successful RHS retains the saved leaf, latest mixed heap and
exact descriptor effect before the structural writeback suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhsReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution) (leaf : TypeSystem.Ty)
    (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  meaning : CompatibleCellPlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
    (faults := faults) resolution id node lowered environment (.value right) heap (.inRight .word value) store mapping world
  related : ValueRep checked registry functions mapping world leaf right value prepared.route.leafType


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhsReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterReflection
/-! Every actual completed live compatible setter has an independent source
update, exact raw missing-default fault, or absent-root fault. The source outcome
is constructed from static path/authentication receipts and the common heap;
no source update trace or helper execution is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces
open CompatiblePlaceSetterReflection (ResultRep)

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
  {path : PreparedPath compilation.checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression replacementExpression : Expr}
  {replacement : Dynamic.Value} {replacementValue : Value}
  {identities : Dynamic.Value → Word → Prop}

private theorem present_evaluates
    {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead compilation.checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  rcases CompatiblePlaceReadTotality.read_or_fault arguments functionTypes root.payload replacementRep.projection with
      ⟨selected, _, read, _⟩ | ⟨reason, fault⟩
  · obtain ⟨updated, changed⟩ := DataPlaceUpdateTotality.read_update read replacement
    have tree := arguments.updateTree root.payload replacementRep changed prepared
    obtain ⟨native, after, administrative, represented, evaluated, appended, _⟩ :=
      CompatiblePlaceWriteback.setter_at root tree nonempty faithful observations keyLength environment keyType
        referenceExpression keyExpression replacementExpression referenceSelected keysSelected replacementSelected
    obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated,
      .updated root.input.initial changed (represented.extend (.refl _) (.refl _) extension),
      finalHeaps, extension, frame, appended⟩
  · obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
    obtain ⟨after, administrative, evaluated, appended, _⟩ :=
      CompatiblePlaceSetterFault.setter_at root tree nonempty faithful observations keyLength environment keyType
        referenceExpression keyExpression replacementExpression replacementValue referenceSelected keysSelected replacementSelected
    obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated, .missing root.input.initial fault receipt,
      finalHeaps, extension, frame, appended⟩

private theorem resolved_nonempty
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (nonempty : prepared.steps ≠ []) : resolved ≠ [] := by
  have general : ∀ {root leaf projections position steps sites}
      {path : PreparedPath compilation.checked source site root projections position steps sites leaf} {resolved},
      Arguments compilation.checked registry functions mapping world source site keys path resolved → steps.length = resolved.length := by
    intro root leaf projections position steps sites path resolved arguments
    induction arguments with
    | nil => rfl
    | member _ ih | index _ _ _ ih => exact congrArg Nat.succ ih
  have length := general arguments
  intro empty
  rw [empty, List.length_nil] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length)

/-- Construct finite execution of the real live setter, including its source
classification and any administrative suffix, from authenticated live inputs. -/
theorem evaluates
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (cellOrdinary : cell.generalized = none)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨optional, native, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells heaps reference read cellOrdinary
  cases represented with
  | initialized related =>
    exact present_evaluates (.initialized read reference native related) arguments replacementRep nonempty functionTypes
      faithful observations keyLength heaps environmentTyped helperTyped referenceSelected keysSelected replacementSelected
  | @uninitialized sourceType payload projected =>
    by_cases mappingRoot : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingRoot
      obtain ⟨rootValue, root⟩ := RootRead.virtual (virtual key value rfl) registryExtension projected read reference native
      exact present_evaluates root arguments replacementRep nonempty functionTypes faithful observations keyLength
        heaps environmentTyped helperTyped referenceSelected keysSelected replacementSelected
    · have noVirtual := ordinary (fun key value same => mappingRoot ⟨key, value, same⟩)
      have evaluated : Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
          (.inLeft prepared.route.rootType (.word prepared.invalidProjection)) store := by
        apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
        cases steps : prepared.steps with
        | nil => exact (nonempty steps).elim
        | cons head tail =>
          simp only [normalizeRoot, noVirtual, LanguageResult.failure]
          exact .caseLeft (.first (.var rfl)) (.inLeft .word)
      exact ⟨_, store, world, [], evaluated, .uninitialized rfl mappingRoot (resolved_nonempty arguments nonempty),
        heaps, .refl _, .refl _ _, by simp⟩

/-- Actual completed native execution determines an independent source
outcome without a prior source trace or a helper-execution certificate. -/
theorem reflects
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (cellOrdinary : cell.generalized = none)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue)
    {result : Value} {after : Store}
    (completed : Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after) :
    ∃ futureWorld administrative,
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨actual, actualStore, futureWorld, administrative, evaluated, resultRep, heaps, worlds, frame, appended⟩ :=
    evaluates ordinaryCells cellOrdinary arguments replacementRep virtual ordinary registryExtension nonempty functionTypes faithful observations keyLength
      heaps reference read environmentTyped helperTyped referenceSelected keysSelected replacementSelected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨futureWorld, administrative, resultRep, heaps, worlds, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceWriteback
/-! The compatible setter reads the latest optional root, rebuilds its actual
raw carrier, and writes the mapped source cell once. Administrative helper
allocations extend the existing world and preserve the common source heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceWriteback
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- A successful independent reconstruction and source write derive the
actual setter evaluation and native mapped write. No helper run is assumed. -/
theorem preserves
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (ordinary : cell.generalized = none)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {replacementSource updated : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked registry functions mapping world leaf replacementSource replacement prepared.route.leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some sourceRoot) projections updated)
    {after : Dynamic.Heap} (written : Dynamic.Heap.Writes heap location (some updated) after)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native helperStore finalStore futureWorld,
      ValueRep checked registry functions mapping futureWorld cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) helperStore ∧
      helperStore.read? target = some optional ∧
      helperStore.write? target (.inRight .unit native) = some finalStore ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld after finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping futureWorld after finalStore := by
  have tree := arguments.updateTree root.payload replacementRep changed prepared
  obtain ⟨native, helperStore, administrative, related, evaluated, appended, _⟩ :=
    CompatiblePlaceWriteback.setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, helperHeaps, _, frame⟩ :=
    CellMappingHeap.evaluation_preserves_frame heaps environmentTyped setterTyped evaluated appended
  have related := related.extend (.refl _) (.refl _) extension
  obtain ⟨finalStore, nativeWrite, finalHeaps, writeFrame⟩ :=
    helperHeaps.write_initialized ordinaryCells (root.reference.extend (.refl _) extension) root.sourceRead ordinary related written
  have nativeRead : helperStore.read? target = some optional := by
    rw [appended]
    simpa [Store.read?, List.getElem?_append_left (heaps.target_lt root.reference.mapped)] using root.nativeRead
  exact ⟨native, helperStore, finalStore, futureWorld, related, evaluated, nativeRead, nativeWrite,
    finalHeaps, extension, frame.trans writeFrame, Dynamic.HeapMetadataExtend.of_write written,
    (appended.symm ▸ CellAwareScopeAuthority.Effect.append store administrative
      (.refl heap) (.refl mapping) extension).trans
      (CellAwareScopeAuthority.Effect.write_ordinary helperHeaps.injective root.sourceRead ordinary
        (root.reference.extend (.refl _) extension) written nativeWrite)⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceWriteback
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterFault
/-! A structural source fault in the latest root derives a failed actual setter
load. The raw key guard and missing-default metadata come from the independent
fault trace. Administrative comparisons may allocate; no source cell is written.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterFault
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- The source fault automatically supplies the exact token and fault tree.
Finite Core preservation and the real administrative suffix transport the
common heap; the latest source and native root remain unchanged. -/
theorem preserves {cells : GenericHeap.CellModel ambient.definitions}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) projections reason)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {replacement : Value}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ token count after administrative futureWorld,
      FaultToken checked registry sourceRoot prepared.steps projections reason token count ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, evaluated, appended, counted⟩ :=
    CompatiblePlaceSetterFault.setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression replacement
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ := CellMappingHeap.evaluation_preserves_frame heaps environmentTyped setterTyped evaluated appended
  exact ⟨token, count, after, administrative, futureWorld, receipt, evaluated,
    finalHeaps, extension, frame,
    by rw [appended]; exact root.after_append extension, appended, counted⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterFault
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
/-! The common target prefix evaluates every key once and then reads the live
source root metadata. It does not assume that structural selection succeeds.
The receipt below is a semantic output; compiler certificates remain static. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared) (place : PlaceResolution)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (location : Dynamic.Location) (resolved : List Dynamic.EvaluatedProjection)
    (coreEnvironment : Environment) (before after : Dynamic.Heap) (store : Store)
    (mapping : LocationMap) (world : StoreTyping) (index : Nat) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  keyStore : Store
  keyMap : LocationMap
  keyWorld : StoreTyping
  cell : Dynamic.Cell
  read : Dynamic.Heap.Reads after location cell
  ordinary : cell.generalized = none
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents keyMap keyWorld location target prepared.route.rootType
  selected : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  shaped : DataPlaceKeyOrder.Values place.projections sources resolved
  evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  related : DataExpressionSequence.Values (payloadModel checked registry functions) keyMap keyWorld sourceTypes (codes.map (·.type)) sources values
  heaps : GenericHeap.CellHeapRepresents cells keyMap keyWorld after keyStore
  maps : LocationMap.Extends mapping keyMap
  worlds : WorldExtends world keyWorld
  frame : AdministrativePreserved mapping store keyMap keyStore
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances mapping world before store keyMap keyWorld after keyStore


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceGetterReflection
/-! Every actual completed live compatible getter has an independent source
read, exact raw missing-default fault, or absent-root fault. The source outcome
is constructed from static path/authentication receipts and the common heap;
no source projection trace or helper execution is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceGetterReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces
open CompatiblePlaceGetterReflection (ResultRep)

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
  {path : PreparedPath compilation.checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}
  {identities : Dynamic.Value → Word → Prop}

private theorem present_evaluates
    {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead compilation.checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  rcases CompatiblePlaceReadTotality.read_or_fault arguments functionTypes root.payload leafProjected with
      ⟨selected, _, read, _⟩ | ⟨reason, fault⟩
  · have tree := arguments.readTree root.payload leafProjected read prepared
    obtain ⟨native, after, administrative, initial, _, represented, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated,
      .read initial read (represented.extend (.refl _) (.refl _) extension),
      finalHeaps, extension, frame, appended⟩
  · obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
    obtain ⟨after, administrative, initial, _, evaluated, appended, _⟩ :=
      faultTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated, .missing initial fault receipt,
      finalHeaps, extension, frame, appended⟩

private theorem resolved_nonempty
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (nonempty : prepared.steps ≠ []) : resolved ≠ [] := by
  have general : ∀ {root leaf projections position steps sites}
      {path : PreparedPath compilation.checked source site root projections position steps sites leaf} {resolved},
      Arguments compilation.checked registry functions mapping world source site keys path resolved → steps.length = resolved.length := by
    intro root leaf projections position steps sites path resolved arguments
    induction arguments with
    | nil => rfl
    | member _ ih | index _ _ _ ih => exact congrArg Nat.succ ih
  have length := general arguments
  intro empty
  rw [empty, List.length_nil] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length)

/-- Construct finite execution of the real live getter, including its source
classification and any administrative suffix, from authenticated live inputs. -/
theorem evaluates
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (cellOrdinary : cell.generalized = none)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨optional, native, represented⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells heaps reference read cellOrdinary
  cases represented with
  | initialized related =>
    exact present_evaluates (.initialized read reference native related) arguments leafProjected nonempty functionTypes
      faithful observations keyLength heaps environmentTyped helperTyped referenceSelected keysSelected
  | @uninitialized sourceType payload projected =>
    by_cases mappingRoot : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingRoot
      obtain ⟨rootValue, root⟩ := RootRead.virtual (virtual key value rfl) registryExtension projected read reference native
      exact present_evaluates root arguments leafProjected nonempty functionTypes faithful observations keyLength
        heaps environmentTyped helperTyped referenceSelected keysSelected
    · have noVirtual := ordinary (fun key value same => mappingRoot ⟨key, value, same⟩)
      have evaluated : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
          (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
        apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (keysSelected.evaluates store))
        cases steps : prepared.steps with
        | nil => exact (nonempty steps).elim
        | cons head tail =>
          simp only [normalizeRoot, noVirtual, LanguageResult.failure]
          exact .caseLeft (.first (.var rfl)) (.inLeft .word)
      exact ⟨_, store, world, [], evaluated, .uninitialized rfl mappingRoot (resolved_nonempty arguments nonempty),
        heaps, .refl _, .refl _ _, by simp⟩

/-- Actual completed native execution determines an independent source
outcome without a prior source trace or a helper-execution certificate. -/
theorem reflects
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (cellOrdinary : cell.generalized = none)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    {result : Value} {after : Store}
    (completed : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after) :
    ∃ futureWorld administrative,
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨actual, actualStore, futureWorld, administrative, evaluated, resultRep, heaps, worlds, frame, appended⟩ :=
    evaluates ordinaryCells cellOrdinary arguments leafProjected virtual ordinary registryExtension nonempty functionTypes faithful observations keyLength
      heaps reference read environmentTyped helperTyped referenceSelected keysSelected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨futureWorld, administrative, resultRep, heaps, worlds, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceGetterReflection
end
