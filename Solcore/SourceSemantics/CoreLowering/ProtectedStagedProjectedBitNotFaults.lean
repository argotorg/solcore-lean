import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPreservation

/-! Pure failure phases consume the actual completed key execution.
The live root, fault token, reached diagnostic receipt, and caller transition
remain tied to that execution; no child-meaning callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

theorem preserves_projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatiblePlaceTargetKeys.Execution compilation.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ reason token := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keyState, keyStateRelated⟩ := keyPost
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists : ∃ optional rootValue,
      RootRead compilation.checked registry functions keys.keyMap keys.keyWorld prepared after keys.keyStore location keys.target
        currentCell optional sourceRoot rootValue := by
    cases initialValue with
    | initialized =>
      obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keys.heaps keys.reference currentRead
      exact ⟨_, value, root⟩
    | emptyMapping key value =>
      obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keys.heaps keys.reference currentRead
        (layout.virtual key value cellType.symm) registryExtension
      exact ⟨_, native, root⟩
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
    simpa only [renamedCodes_types] using keys.related
  have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keyRelated.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keyRelated)
      (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
  obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
    evaluation_frame (mapping := keys.keyMap) keys.heaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
  let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata,
    reached, protocol.trans keyStateRelated phaseRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
      currentCell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
      keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType, currentArguments, fault, receipt, tree⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

theorem preserves_uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatiblePlaceTargetKeys.Execution compilation.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.UninitializedPost compilation.checked registry functions protocol environment place prepared initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ location := by
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference currentRead
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  obtain ⟨keyState, keyRelated⟩ := keyPost
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata,
    keyState, keyRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target, currentCell,
      .inLeft prepared.route.rootType .unit, keys.sources, resolved, keyRelated, protocol.refl keyState, rfl, rfl, rfl,
      .refl _, .refl _ _, lookup, currentRead, keys.reference, native, absent ▸ represented, cellType, empty, notMapping, layout.nonempty, keys.shaped, hasProjection⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults
