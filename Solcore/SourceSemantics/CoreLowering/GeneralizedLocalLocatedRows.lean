import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedCellAllocation
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! A generalized declaration retains its exact lexical compiler binding and
the native row created at its actual source location. Source metadata transport
and native row transport remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap GenericHeap SourceCoreLocalPolymorphism
open GeneralizedLocalDescriptorHeap

variable {definitions : Core.DataEnvironment} {model : InstanceModel definitions}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}

structure Attachment (model : InstanceModel definitions) (function : Dynamic.GeneralizedClosure)
    (binding : Binding) (lexical : Substitution) : Prop where
  registered : model.locals.binding binding.caller binding.binder.id = .ok binding
  captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
    function.captured function.binder function.initializer function
  origin : model.Origin function binding lexical
  binder : function.binder.id = binding.binder.id
  initializer : function.initializer = binding.initializer

structure Located (model : InstanceModel definitions) (function : Dynamic.GeneralizedClosure)
    (binding : Binding) (lexical : Substitution) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  attachment : Attachment model function binding lexical
  cell : Dynamic.Cell
  sourceRead : Dynamic.Heap.Reads heap location cell
  descriptor : cell.generalized = some function
  target : Core.Location
  reference : ReferenceRepresents mapping world location target (binding.bundleType lexical)
  values : List Core.Value
  rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
    (binding.atContext lexical) values
  nativeRead : store.read? target = some (.inRight .unit (ProductBundle.value values))

theorem Attachment.stored (attachment : Attachment model function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values) :
    Stored model mapping world function (ProductBundle.value values) (binding.bundleType lexical) :=
  .bundle binding lexical attachment.registered attachment.captures attachment.origin
    attachment.binder attachment.initializer rows

private theorem extend_rows {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {candidates : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) candidates values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ProductBundle.Pointwise (model.Represents futureMapping futureWorld function binding lexical) candidates values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.extend head maps worlds) ih

/-- Metadata extension preserves the actual descriptor. The stored native row
is retained only when its real location still contains that same value. -/
theorem Located.extend {location : Dynamic.Location} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store updated : Store}
    (located : Located model function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (nativeRead : updated.read? located.target = some (.inRight .unit (ProductBundle.value located.values))) :
    Nonempty (Located model function binding lexical location futureMapping futureWorld after updated) := by
  obtain ⟨cell, sourceRead, _, descriptor⟩ := metadata location located.cell located.sourceRead
  exact ⟨⟨located.attachment, cell, sourceRead, descriptor.trans located.descriptor,
    located.target, ⟨maps.lookup located.reference.mapped, worlds.lookup located.reference.typed⟩,
    located.values, extend_rows located.rows maps worlds, nativeRead⟩⟩

/-- Actual parameter allocation only appends native cells. -/
theorem Located.append {location : Dynamic.Location} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store : Store} (suffix : Store)
    (located : Located model function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Nonempty (Located model function binding lexical location futureMapping futureWorld after (store ++ suffix)) := by
  apply located.extend metadata maps worlds
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp located.nativeRead).1).trans located.nativeRead

/-- Administrative frame changes are disjoint from the mapped descriptor. -/
theorem Located.set_unmapped {location : Dynamic.Location} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {target : Core.Location} (value : Core.Value) (unmapped : target ∉ mapping) :
    Nonempty (Located model function binding lexical location mapping world heap (store.set target value)) := by
  have different : target ≠ located.target := by
    intro same
    exact unmapped (same.symm ▸ List.mem_of_getElem? located.reference.mapped)
  apply located.extend (.refl heap) (.refl mapping) (.refl world)
  simpa [Store.read?, different] using located.nativeRead

/-- A write to an ordinary Source cell cannot overwrite this descriptor's
native row. The separation comes from actual reads and map injectivity. -/
theorem Located.write_ordinary {location writtenLocation : Dynamic.Location} {mapping : LocationMap}
    {world : StoreTyping} {heap after : Dynamic.Heap} {store updated : Store}
    (located : Located model function binding lexical location mapping world heap store)
    (injective : LocationMap.Injective mapping)
    {cell : Dynamic.Cell} {writtenTarget : Core.Location} {payload : Core.Ty}
    (sourceRead : Dynamic.Heap.Reads heap writtenLocation cell) (ordinary : cell.generalized = none)
    (reference : ReferenceRepresents mapping world writtenLocation writtenTarget payload)
    {sourceValue : Option Dynamic.Value} {nativeValue : Core.Value}
    (written : Dynamic.Heap.Writes heap writtenLocation sourceValue after)
    (nativeWritten : store.write? writtenTarget nativeValue = some updated) :
    Nonempty (Located model function binding lexical location mapping world after updated) := by
  have different : location ≠ writtenLocation := by
    intro same
    subst writtenLocation
    have cells := located.sourceRead.functional sourceRead
    have descriptors := congrArg Dynamic.Cell.generalized cells
    rw [located.descriptor, ordinary] at descriptors
    cases descriptors
  have nativeDifferent : located.target ≠ writtenTarget := by
    intro same
    have indices := injective (same ▸ located.reference.mapped) reference.mapped
    apply different
    cases location
    cases writtenLocation
    exact congrArg Dynamic.Location.mk indices
  apply located.extend (.of_write written) (.refl mapping) (.refl world)
  exact (Store.write?_preserves_other nativeWritten nativeDifferent).trans located.nativeRead

/-- This is the actual three-cell marked allocation used by the compiler. -/
theorem of_marked_allocation {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location} {values : List Core.Value}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary model) mapping world before store)
    (attachment : Attachment model function binding lexical)
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
    CellHeapRepresents (cellModel ordinary model) (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
    Nonempty (Located model function binding lexical location (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)])) := by
  obtain ⟨afterHeaps, reference⟩ := CallableIndexedCellAllocation.heap_allocate heaps snapshotTyped markerTyped
    (CellRepresents.generalized (attachment.stored rows)) (.generalized allocated)
  refine ⟨afterHeaps, ⟨⟨attachment, _, allocated.reads_new, rfl, _, reference, values,
    extend_rows rows ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩⟩⟩
  simp [Store.read?]

theorem of_marked_allocation_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location} {values : List Core.Value}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary model) mapping world before store)
    (attachment : Attachment model function binding lexical)
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
    CellHeapRepresents (cellModel ordinary model) (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
    (∃ located : Located model function binding lexical location (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]), located.values = values) := by
  obtain ⟨afterHeaps, reference⟩ := CallableIndexedCellAllocation.heap_allocate heaps snapshotTyped markerTyped
    (CellRepresents.generalized (attachment.stored rows)) (.generalized allocated)
  refine ⟨afterHeaps, ⟨⟨attachment, _, allocated.reads_new, rfl, _, reference, values,
    extend_rows rows ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩, rfl⟩⟩
  simp [Store.read?]

private theorem project_readOnly {types : List Core.Ty} {index : Nat} {bundle projection : Core.Expr}
    (restricted : ReadOnly.Expression bundle)
    (selected : ProductBundle.project? types index bundle = some projection) :
    ReadOnly.Expression projection := by
  induction types generalizing index bundle projection with
  | nil => cases selected
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases selected; exact restricted
      | succ index => cases selected
    | cons next remaining =>
      cases index with
      | zero => cases selected; exact .first restricted
      | succ index => exact ih (.second restricted) selected

theorem readOnly {catalog : Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered) :
    ReadOnly.Expression lowered.expression := by
  rw [receipt.emitted]
  exact .caseE (.caseE (.loadCell .var) (.inLeft .word) (.inRight .var))
    (.inLeft .var) (.inRight (project_readOnly .var receipt.projected))

/-- Actual first-match source and native lookups join the read certificate to
the row retained by its declaration. Full candidate context still selects it. -/
theorem Located.preserves {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical : Core.Environment}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location) :
    ∃ native, model.Represents mapping world function binding lexical receipt.candidate native ∧
      Evaluates canonical store lowered.expression (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    simp only [sameCaller, sameBinder, located.attachment.registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  apply GeneralizedLocalBundleReadMeaning.preserves receipt
  · rw [sameRows]
    exact located.rows
  · exact referenceAt
  · exact located.nativeRead

/-- Renaming reads exactly the same existing closure value and store. -/
theorem Located.preserves_rename {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, model.Represents mapping world function binding lexical receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  obtain ⟨native, represented, evaluated⟩ := located.preserves receipt sameCaller sameBinder context environments lookup
  exact ⟨native, represented, (readOnly receipt).evaluation_rename evaluated agrees⟩

theorem Located.reflects_rename {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {before after : Store}
    (located : Located model function binding lexical location mapping world heap before)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming} {output : Core.Value}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (evaluated : Evaluates actual before (lowered.expression.rename embedding) output after) :
    after = before ∧ ∃ native, output = .inRight .word native ∧
      model.Represents mapping world function binding lexical receipt.candidate native := by
  obtain ⟨native, represented, expected⟩ := located.preserves_rename receipt sameCaller sameBinder context environments lookup agrees
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expected
  exact ⟨rfl, native, rfl, represented⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
