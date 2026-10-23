import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceWriteback
import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceLayout
import Solcore.SourceSemantics.CoreLowering.ProtectedState
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement

/-! Projected unary writeback consumes the actual key/getter state. Its Unit
slot is administrative; it creates no Source expression or Source RHS step. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleRenamedPlace
universe u v

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (environment : Environment) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (target : Location) (keys : List Value) (snapshot : Value) (before after : Dynamic.Heap)
    (updated : Dynamic.Value) (operator : Option BinaryOp) (invalid : Word) where
  replacement : Value
  value : Value
  helperStore : Store
  finalStore : Store
  finalWorld : StoreTyping
  related : ValueRep checked registry functions mapping finalWorld prepared.route.rootSourceType updated value prepared.route.rootType
  heaps : GenericHeap.CellHeapRepresents cells mapping finalWorld after finalStore
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store mapping finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances mapping world before store mapping finalWorld after finalStore
  modified : Evaluates (rhsEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit environment) store
    (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
    (.inRight .word replacement) store
  setter : Evaluates (modifiedEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit replacement environment) store
    (.apply (SourceCoreCompatibleDataPlaces.setter prepared (SourceCoreCalls.packArguments codes).type)
      (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word value) helperStore
  read : ∃ optional, helperStore.read? target = some optional
  written : helperStore.write? target (.inRight .unit value) = some finalStore

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: .unit ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

/-- Consume an independent snapshot write and derive its actual native
modifier, latest-root reconstruction and single mapped store update. -/
theorem typed_of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := resolution.snapshotRelated
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) resolution.mapping resolution.world
      sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated
  have reference := resolution.reference
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  cases written with
  | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
    have cellEq := sourceRead.functional resolution.currentRead
    have cellOrdinary : cell.generalized = none := cellEq ▸ resolution.ordinary
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ resolution.currentType
    obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
    rw [resolution.selectedEq] at applies
    obtain ⟨replacement', replacementValue, replacementRep, applies', modifiedEvaluated, _⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile snapshotRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment)
        (.var (index := 1) rfl) operator resolution.store invalid
    have same := CompatiblePlaceBitNotModifier.functional applies' applies
    subst replacement'
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists := CompatibleCellPlaceRoot.root_of_initial ordinaryCells resolution.heaps reference
      sourceRead cellOrdinary initialValue (fun k v same => layout.virtual k v (cellType.symm.trans same)) registryExtension
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have typedEnvironment : RuntimeEnvironmentHasTypes resolution.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit replacementValue coreEnvironment)
        (prepared.route.leafType :: .unit :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons .unit (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken resolution.worlds)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions resolution.mapping resolution.world source site resolution.values
        currentPath target.projections := by simpa only [cellType] using arguments
    obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
      helperRead, coreWritten, finalHeaps, extension, frame, metadata, effect⟩ :=
      CompatibleCellPlaceWriteback.preserves ordinaryCells root resolution.heaps cellOrdinary currentArguments replacementRep changed sourceWrite layout.nonempty
        faithful observations (layout.keyTypes ▸ keyRep.length.2) typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨⟨replacementValue, updatedValue, helperStore, finalStore, finalWorld,
      by simpa only [cellType] using updatedRep, finalHeaps, extension, frame, metadata, effect,
      modifiedEvaluated, ?_, ⟨_, helperRead⟩, coreWritten⟩, ?_⟩
    · simpa only [packed_renamed_type] using setterEvaluated
    · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))

/-- Protected callers carry the actual post-write witness. -/
theorem of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatibleCellPlaceResolution.Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : protocol.State ⟨scope, resolution.mapping, resolution.world, selectedHeap, resolution.store, canonical⟩)
    (related : protocol.Relates initial selected)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : Execution compilation.checked registry functions cells instances prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, resolution.mapping, commit.finalWorld, after, commit.finalStore, canonical⟩ := by
  obtain ⟨commit, typed⟩ := typed_of_write ordinaryCells layout ordinary registryExtension faithful observations profile
    environments agrees actualTyped resolution written operator invalid
  exact ⟨commit, typed, transport.extend selected (.refl _) commit.worlds commit.frame commit.metadata,
    protocol.trans related (transport.related selected (.refl _) commit.worlds commit.frame commit.metadata)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedBitNotCommit
