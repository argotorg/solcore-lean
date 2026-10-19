import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadCompletion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTarget
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence

/-! Staged keys retain their original failure and reached heap. The native
getter runs only after the complete ordered key row, and keeps the existing
prepared route and snapshot representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection CompatibleRenamedPlace CompatibleMixedRoute CompatiblePlaceKeys
universe u v

variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {place : PlaceResolution} {environment : Dynamic.Environment} {actual canonical : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {scope : Scope}

inductive KeyResultAt (size : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) (index : Nat)
    (rhs next : Expr) (output : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before place)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      KeyResultAt size initial index rhs next output operator bitNot invalid value finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location}
      {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (execution : CompatibleCellPlaceTargetKeys.Execution checked registry functions cells instances prepared place codes sourceTypes
        location resolved actual before after store mapping world index)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values execution.sources) after)
      (sourcesTyped : Dynamic.ValuesHaveTypes context after execution.sources sourceTypes)
      (sourceHeap : Dynamic.HeapWellTyped context after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize
        (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) actual) execution.keyStore
        (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next output operator bitNot invalid) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, execution.keyMap, execution.keyWorld, after, execution.keyStore, canonical⟩) :
      KeyResultAt size initial index rhs next output operator bitNot invalid value finalStore

inductive PrefixResultAt (size : Nat) (leaf : TypeSystem.Ty)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhs next : Expr) (output : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (value : Value) (finalStore : Store) : Prop where
  | keyFault {sourceSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before place)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | getterFault {sourceSize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault}
      {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after place sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (execution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf target
        actual store mapping world before after)
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values execution.sources) after)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before after place execution.sources target)
      (sourcesTyped : Dynamic.ValuesHaveTypes context after execution.sources sourceTypes)
      (sourceHeap : Dynamic.HeapWellTyped context after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) actual) execution.store
        (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next output operator bitNot invalid) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore

variable {protocol}

theorem values_plain {size : Nat} {ids : List ExpressionId} {sources : List Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context environment before ids (.values sources) after) :
    Dynamic.ExpressionsEvaluate program context invocation.evidence invocation.source environment before ids sources after := by
  induction ids generalizing size before sources with
  | nil => cases trace; exact .nil
  | cons id ids ih =>
      cases trace with
      | cons head tail => exact .cons head.sound.value_plain (ih tail)


theorem reflects_keys (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions} {program : Program} {context : SourceSemantics.Context}
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {scope : Scope}
    {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (_children : DataExpressionSequence.Tree invocation.source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∀ {keySize keyValue keyStore},
      EvaluationSize keySize (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
        ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ)) keyValue keyStore →
      keySize < budget →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
          (Staging.Recursive.ProjectedTarget.keys place.projections) outcome after ∧
        RecursiveStageArguments.ResultFor (payloadModel checked registry functions) finalMap finalWorld sourceTypes codes faults outcome keyValue ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after keyStore ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    KeyResultAt (cells := cells) (instances := instances) (checked := checked) (registry := registry) (functions := functions) (program := program)
      (context := context) (stages := stages) (invocation := invocation) (faults := faults)
      (prepared := prepared) (codes := renamedCodes codes ξ) (sourceTypes := sourceTypes)
      (place := place) (environment := environment) (actual := coreEnvironment)
      protocol size initialState (ξ index) rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have reflectKeys := fun {keySize : Nat} {keyValue : Value} {keyStore : Store}
      (evaluated : CoreProof.EvaluationSize keySize (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) keyValue keyStore) (keyBound : keySize < size) =>
    sequenceMeaning target (agrees selected) (.cons (.cellRef reference.typed) actualTyped)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated) (Nat.lt_of_lt_of_le keyBound bounded)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated.sound (Evaluates.var (agrees selected))
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, effect, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | fault tokenRep =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.intro lookup initialRead) sourceTrace rfl tokenRep finalHeaps maps worlds frame metadata effect post
    | caseRight keysEvaluated tail =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, effect, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | @values sources values related =>
        obtain ⟨resolved, shaped, _plain⟩ := DataPlaceKeyOrder.values_projections
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using values_plain sourceTrace)
        obtain ⟨scheme, staticLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
        obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
        have locationEq := lookup.functional staticLookupRuntime
        subst staticLocation
        have cellEq := initialRead.functional staticRead
        subst staticCell
        obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
        exact .keys lookup
          ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
            (locals.mono metadata).descriptor_empty_of_monomorphic (sourceHeap _ rfl).2 staticLookup lookup read monomorphic,
            type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
            keysEvaluated.sound, by simpa only [renamedCodes_types] using related, finalHeaps, maps, worlds, frame, metadata, effect⟩ sourceTrace (sourceHeap _ rfl).1 (sourceHeap _ rfl).2 (by omega) tail post

theorem reflects_getter (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    {program : Program} {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation invocation.source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      invocation.source site place prepared leaf initialState (fun reason token => faults (.semantic reason) token))
    (uninitializedFor : ProtectedPlaceReachedDiagnostics.UninitializedFor compilation.checked registry functions protocol
      environment place prepared initialState (fun reason token => faults (.semantic reason) token))
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∀ {keySize keyValue keyStore},
      EvaluationSize keySize (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
        ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ)) keyValue keyStore →
      keySize < budget →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
          (Staging.Recursive.ProjectedTarget.keys place.projections) outcome after ∧
        RecursiveStageArguments.ResultFor (payloadModel compilation.checked registry functions) finalMap finalWorld sourceTypes codes faults outcome keyValue ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after keyStore ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    PrefixResultAt (cells := cells) (instances := instances) (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (stages := stages) (invocation := invocation) (faults := faults)
      (prepared := prepared) (codes := renamedCodes codes ξ) (sourceTypes := sourceTypes)
      (place := place) (environment := environment) (actual := coreEnvironment)
      protocol size leaf initialState rhs next outputType operator bitNot invalid result finalStore := by
  have closed := virtual_closed layout ordinary
  have getterTyped := getter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := reflects_keys budget layout.children protocol environments heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead completed bounded
  cases keyPhase with
  | fault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata effect post =>
    exact .keyFault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata effect post
  | @keys keySourceSize keyTailSize sourceLocation resolved after keyLookup keys sourceTrace sourcesTyped sourceHeap keyBound continuation keyPost =>
    obtain ⟨keyState, keyStateRelated⟩ := keyPost
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
      simpa only [renamedCodes_types] using keys.related
    have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked invocation.source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld invocation.source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keyRelated)
        (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatibleCellPlaceGetterReflection.reflects ordinaryCells keys.ordinary currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keyRelated.length.2)
        keys.heaps keys.reference keys.read typedEnvironment getterTyped (.var rfl) (.var rfl) evaluated
    unfold CompatiblePlaceKeyReflection.remainder at continuation
    simp only [packed_renamed_type] at continuation
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, administrative, resultRep, finalHeaps, extension, frame, appended⟩ := reflectGetter getterEvaluated.sound
      have getterEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) keys.keyStore administrative (.refl after) (.refl keys.keyMap) extension
      cases resultRep with
      | @missing sourceRoot reason token count initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := CompatibleCellPlaceRoot.root_of_initial ordinaryCells
              keys.heaps keys.reference keys.read keys.ordinary initial
              (fun k v same => layout.virtual k v (keys.type.symm.trans same)) registryExtension
            obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree live.payload fault prepared
            obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
            let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have witness : ProtectedPlaceReachedDiagnostics.MissingWitness compilation.checked registry functions protocol
                invocation.source site place prepared leaf initialState reached reason token :=
              ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
                keys.cell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
                keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, live, keys.type, currentArguments, fault, receipt, tree⟩
            exact .getterFault sourceTrace (.projection lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read initial fault) rfl
              (missingFor reached (protocol.trans keyStateRelated phaseRelated) witness) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
              (keys.effect.trans getterEffect)
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, native, cellRep⟩ := CompatibleCellPlaceRoot.read_at ordinaryCells keys.heaps keys.reference keys.read keys.ordinary
            let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have witness : ProtectedPlaceReachedDiagnostics.UninitializedWitness compilation.checked registry functions protocol
                environment place prepared initialState reached location :=
              ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target,
                keys.cell, optional, keys.sources, resolved, keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame,
                lookup, keys.read, keys.reference, native, cellRep, keys.type, empty, notMapping, layout.nonempty, keys.shaped, nonempty⟩
            exact .getterFault sourceTrace (.uninitialized lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read empty notMapping nonempty) rfl
              (uninitializedFor reached (protocol.trans keyStateRelated phaseRelated) witness) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
              (keys.effect.trans getterEffect)
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, administrative, resultRep, finalHeaps, extension, frame, appended⟩ := reflectGetter getterEvaluated.sound
      have getterEffect := appended.symm ▸ CellAwareScopeAuthority.Effect.append
        (instances := instances) keys.keyStore administrative (.refl after) (.refl keys.keyMap) extension
      cases resultRep with
      | @read sourceRoot selected snapshot initial read represented =>
        refine .resolved
          { target := keys.target
            sources := keys.sources
            values := keys.values
            selected := selected
            snapshot := snapshot
            keyStore := keys.keyStore
            store := _
            mapping := keys.keyMap
            world := futureWorld
            selectedEq := rfl
            currentCell := keys.cell
            currentRead := keys.read
            ordinary := keys.ordinary
            currentType := keys.type
            reference := keys.reference.extend (.refl _) extension
            shaped := keys.shaped
            keysEvaluated := keys.evaluated
            snapshotEvaluated := by simpa only [packed_renamed_type] using getterEvaluated.sound
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata
            effect := keys.effect.trans getterEffect } sourceTrace
          (.intro lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read initial read)
          sourcesTyped sourceHeap ?_ (by simpa only [CompatiblePlacePrefixReflection.remainder, packed_renamed_type, snapshotEnvironment] using remaining)
          ⟨transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
            protocol.trans keyStateRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩
        omega


end Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix
