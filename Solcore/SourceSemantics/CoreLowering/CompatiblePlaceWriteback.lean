import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.CompatiblePathUpdates

/-! The compatible setter reads the latest optional root, rebuilds its actual
raw carrier, and writes the mapped source cell once. Administrative helper
allocations extend the existing world and preserve the common source heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- The argument contains a real load. Only the local reference, already
evaluated keys, and replacement use pure selection receipts. -/
theorem setter_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {replacementSource updated : Dynamic.Value} {replacement : Value}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement
      cell.type sourceRoot rootValue prepared.route.rootType prepared.steps projections updated count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression replacementExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native after administrative,
      ValueRep checked registry functions mapping world cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) after ∧ after = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨native, after, administrative, _, related, evaluated, appended, counted⟩ := tree.preserves faithful observations keyLength
    (rootValue :: input :: environment) store prepared.route.rootType
    (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
  refine ⟨native, after, administrative, related, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead)
    (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- A successful independent reconstruction and source write derive the
actual setter evaluation and native mapped write. No helper run is assumed. -/
theorem preserves
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
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
      HeapRepresents checked registry functions mapping futureWorld after finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after := by
  have tree := arguments.updateTree root.payload replacementRep changed prepared
  obtain ⟨native, helperStore, administrative, related, evaluated, appended, _⟩ :=
    setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, storeTyped, _, frame⟩ :=
    evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped setterTyped evaluated appended
  have helperHeaps := CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended
  have related := related.extend (.refl _) (.refl _) extension
  obtain ⟨finalStore, nativeWrite, finalHeaps, writeFrame⟩ :=
    helperHeaps.write_initialized (root.reference.extend (.refl _) extension) root.sourceRead related written
  have nativeRead : helperStore.read? target = some optional := by
    rw [appended]
    simpa [Store.read?, List.getElem?_append_left (heaps.target_lt root.reference.mapped)] using root.nativeRead
  exact ⟨native, helperStore, finalStore, futureWorld, related, evaluated, nativeRead, nativeWrite,
    finalHeaps, extension, frame.trans writeFrame, Dynamic.HeapMetadataExtend.of_write written⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
