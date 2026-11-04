import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments
import Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier

/-!
# Protected contracts: staged projected writes

Staged projected assignments by phase: prefix, resolution, commit, tail and faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedPrefix
/-! Staged keys retain their original failure and reached heap. The native
getter runs only after the complete ordered key row, and keeps the existing
prepared route and snapshot representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedPrefix
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection CompatibleRenamedPlace CompatibleMixedRoute CompatiblePlaceKeys
universe u v

variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
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
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      KeyResultAt size initial index rhs next output operator bitNot invalid value finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location}
      {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes
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
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | getterFault {sourceSize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault}
      {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages sourceSize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after place sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      PrefixResultAt size leaf initial rhs next output operator bitNot invalid value finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
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
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {scope : Scope}
    {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (_children : DataExpressionSequence.Tree invocation.source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents checked registry functions mapping world before store)
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
        HeapRepresents checked registry functions finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    KeyResultAt (checked := checked) (registry := registry) (functions := functions) (program := program)
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
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | fault tokenRep =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.intro lookup initialRead) sourceTrace rfl tokenRep finalHeaps maps worlds frame metadata post
    | caseRight keysEvaluated tail =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, sourceHeap, post⟩ := reflectKeys keysEvaluated (by omega)
      cases represented with
      | @values sources values related =>
        obtain ⟨resolved, shaped, _plain⟩ := DataPlaceKeyOrder.values_projections
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using values_plain sourceTrace)
        obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
        obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
        have locationEq := lookup.functional staticLookupRuntime
        subst staticLocation
        have cellEq := initialRead.functional staticRead
        subst staticCell
        obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
        exact .keys lookup
          ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
            type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
            keysEvaluated.sound, by simpa only [renamedCodes_types] using related, finalHeaps, maps, worlds, frame, metadata⟩ sourceTrace (sourceHeap _ rfl).1 (sourceHeap _ rfl).2 (by omega) tail post

theorem reflects_getter (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
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
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
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
        HeapRepresents compilation.checked registry functions finalMap finalWorld after keyStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    {size : Nat} (completed : CoreProof.EvaluationSize size coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) (bounded : size ≤ budget) :
    PrefixResultAt (checked := compilation.checked) (registry := registry) (functions := functions)
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
  | fault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata post =>
    exact .keyFault ready sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata post
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
      CompatiblePlaceGetterReflection.reflects currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keyRelated.length.2)
        keys.heaps keys.reference keys.read typedEnvironment getterTyped (.var rfl) (.var rfl) evaluated
    unfold CompatiblePlaceKeyReflection.remainder at continuation
    simp only [packed_renamed_type] at continuation
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated.sound
      cases resultRep with
      | @missing sourceRoot reason token count initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := ProtectedPlaceReachedDiagnostics.root_of_initial
              keys.heaps keys.reference keys.read initial
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
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, native, cellRep⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference keys.read
            let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
            have witness : ProtectedPlaceReachedDiagnostics.UninitializedWitness compilation.checked registry functions protocol
                environment place prepared initialState reached location :=
              ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target,
                keys.cell, optional, keys.sources, resolved, keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame,
                lookup, keys.read, keys.reference, native, cellRep, keys.type, empty, notMapping, layout.nonempty, keys.shaped, nonempty⟩
            exact .getterFault sourceTrace (.uninitialized lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read empty notMapping nonempty) rfl
              (uninitializedFor reached (protocol.trans keyStateRelated phaseRelated) witness) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
              ⟨reached, protocol.trans keyStateRelated phaseRelated⟩
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated.sound
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
            metadata := keys.metadata } sourceTrace
          (.intro lookup initialRead (Staging.Recursive.ProjectedTarget.Values.of_data keys.shaped) keys.read initial read)
          sourcesTyped sourceHeap ?_ (by simpa only [CompatiblePlacePrefixReflection.remainder, packed_renamed_type, snapshotEnvironment] using remaining)
          ⟨transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
            protocol.trans keyStateRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩
        omega


end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedResolution
/-! A successful staged key row supplies the actual native key execution.
The pure getter uses the reached live root and the same saved projection keys. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceResolution CompatibleRenamedPlace
universe u v

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {sources : List Dynamic.Value}
    (keysMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ∃ values keyStore keyMap keyWorld,
        Evaluates (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment) store
          ((SourceCoreCalls.packArguments codes).expression.rename (DataPlaceChildExpressions.prefixRenaming 1 ξ))
          (.inRight .word (packValues values)) keyStore ∧
        DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keyMap keyWorld
          sourceTypes (codes.map (·.type)) sources values ∧
        HeapRepresents compilation.checked registry functions keyMap keyWorld after keyStore ∧
        LocationMap.Extends mapping keyMap ∧ WorldExtends world keyWorld ∧
        AdministrativePreserved mapping store keyMap keyStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, keyMap, keyWorld, after, keyStore, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before after place sources sourceTarget) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      execution.sources = sources ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧ Dynamic.HeapWellTyped context after ∧
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩ := by
  cases snapshot with
  | @intro sourceLocation initialCell currentCell projections initial selected lookup initialRead ordered currentRead initialValue selection =>
    have shaped := ordered.to_data
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    obtain ⟨values, keyStore, keyMap, keyWorld, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata, sourceValues, sourceHeap, keyPost⟩ :=
      keysMeaning target (agrees coreLookup) (.cons (.cellRef reference.typed) actualTyped)
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) (actualTyped.weaken keyWorlds))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := keyMap) keyHeaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
    obtain ⟨keyState, keyRelated⟩ := keyPost
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := by simpa only [packed_renamed_type] using evaluated
              keysRelated := by simpa only [renamedCodes_types] using keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, rfl, sourceValues, sourceHeap, agrees coreLookup,
      transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
      protocol.trans keyRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedTail
/-! Native writeback reflection keeps the already established staged keys and
RHS outside its pure suffix. Its result is the real latest-root write or the
structural fault at that RHS heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedTail
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTailReflection CompatibleRenamedPlace
universe u v

inductive ResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (operator : Syntax.ValueAssignOp) (target : Dynamic.ResolvedPlace) (right : Dynamic.Value) (rhsHeap : Dynamic.Heap)
    (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.ProjectedTarget.WriteFault operator target right rhsHeap reason)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld rhsHeap finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before rhsHeap)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩) :
      ResultAt protocol size checked registry functions faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
  | committed {remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement) rhsHeap target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt protocol size checked registry functions faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
private theorem resolved_type {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before targetHeap : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads targetHeap target.location cell) : target.rootType = cell.type := by
  cases trace with
  | intro _ _ _ currentRead _ _ => exact congrArg Dynamic.Cell.type (currentRead.functional read)

private theorem absent_initial {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type)
    (empty : cell.value = none) (notMapping : ¬ ∃ k v, cell.type = .mapping k v) :
    Dynamic.RootInitialValue cell none := by
  cases related with
  | initialized => cases empty
  | uninitialized => exact .uninitialized notMapping

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    {target : Dynamic.ResolvedPlace}
    {sourceSize rhsSize size : Nat}
    (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (right : CompatiblePlaceRhsReflection.Execution compilation.checked registry functions program context evidence source faults environment
      prepared (renamedCodes codes ξ) sourceTypes place leaf target coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
    (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhsState : protocol.State ⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩)
    (rhsRelated : protocol.Relates initialState rhsState)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      source site place prepared leaf initialState faults)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : CoreProof.EvaluationSize size (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    ResultAt protocol size compilation.checked registry functions faults
      prepared (SourceCoreCalls.packArguments codes).type actualContext operator target right.right right.heap coreEnvironment
      before store mapping world scope canonical initialState next outputType result finalStore := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := right.meaning.saved_snapshot
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) right.mapping right.world sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated.extend right.meaning.maps right.meaning.worlds
  have reference := resolution.reference.extend right.meaning.maps right.meaning.worlds
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have targetType := (resolved_type sourceTrace.sound resolution.currentRead).trans resolution.currentType
  obtain ⟨latest⟩ := right.meaning.latest
  have cellType : latest.cell.type = target.rootType := latest.type.trans targetType.symm
  obtain ⟨replacement, replacementValue, replacementRep, applied, modified, _⟩ :=
    CompatiblePlaceModifier.initialized_success observations profile snapshotRep right.related
      (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment)
      (.var (index := 1) rfl) (.var (index := 0) rfl) right.store invalid
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases impossible
  | caseRight modifiedEvaluated remaining =>
    obtain ⟨same, storeEq⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases same
    subst_vars
    have typedEnvironment : RuntimeEnvironmentHasTypes right.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans right.meaning.worlds))))))
    have currentPath : PreparedPath compilation.checked source site latest.cell.type place.projections 0 prepared.steps prepared.keys leaf :=
      latest.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions right.mapping right.world source site resolution.values
        currentPath target.projections := by simpa only [latest.type] using arguments
    have reflectSetter := fun {actual : Value} {after : Store}
        (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment) right.store
          (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
      CompatiblePlaceSetterReflection.reflects currentArguments replacementRep
        (fun k v same => layout.virtual k v (latest.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (latest.type.trans same))) registryExtension layout.nonempty
        functionTypes faithful observations (layout.keyTypes ▸ keyRep.length.2) right.meaning.heaps reference latest.read
        typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
    cases remaining with
    | caseLeft setterEvaluated failed =>
      obtain ⟨futureWorld, _, represented, finalHeaps, extension, frame, _⟩ := reflectSetter setterEvaluated.sound
      cases represented with
      | @missing sourceRoot reason token count root fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := ProtectedPlaceReachedDiagnostics.root_of_initial
              right.meaning.heaps reference latest.read root
              (fun k v same => layout.virtual k v (latest.type.symm.trans same)) registryExtension
            obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree live.payload fault prepared
            obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
            let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have witness : ProtectedPlaceReachedDiagnostics.MissingWitness compilation.checked registry functions protocol
                source site place prepared leaf initialState reached reason token :=
              ⟨⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩, rhsState,
                target.location, resolution.target, latest.cell, optional, sourceRoot, rootValue,
                resolution.values, target.projections, count, currentPath, rhsRelated, phaseRelated,
                rfl, rfl, rfl, extension, frame, live, latest.type, currentArguments, fault, receipt, tree⟩
            exact .fault (.structural latest.read cellType root fault) rfl
              (missingFor reached (protocol.trans rhsRelated phaseRelated) witness)
              finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans frame) (resolution.metadata.trans right.meaning.metadata)
              ⟨reached, protocol.trans rhsRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        have absent := absent_initial latest.related empty notMapping
        exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace.sound rhsTrace.sound latest.read cellType absent nonempty).elim
    | caseRight setterEvaluated remaining =>
      rename_i helperStore helperType updatedValue
      obtain ⟨futureWorld, _, represented, helperHeaps, extension, helperFrame, _⟩ := reflectSetter setterEvaluated.sound
      cases represented with
      | updated root changed updatedRep =>
        cases remaining with
        | letE writeEvaluated continuation =>
          obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _⟩ :=
            CompatiblePlaceCommitReflection.reflects_storeCell helperHeaps (reference.extend (.refl _) extension) latest.read
              updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated.sound
          subst_vars
          have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => resolution.selectedEq.symm ▸ applied)
          let helperState := transport.extend rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)
          exact .committed (.intro latest.read cellType root changed sourceWritten)
            finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
            (((resolution.frame.trans right.meaning.frame).trans helperFrame).trans writeFrame)
            ((resolution.metadata.trans right.meaning.metadata).trans metadata) (slots :=
              [.unit, updatedValue, replacementValue, right.value, .inRight .unit resolution.snapshot, packValues resolution.values,
                .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl
              (by
                change RuntimeEnvironmentHasTypes futureWorld
                  (.unit :: updatedValue :: _) _ _
                exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension)))
              ⟨transport.extend helperState (.refl _) (.refl _) writeFrame metadata,
                protocol.trans (protocol.trans rhsRelated
                  (transport.related rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)))
                  (transport.related helperState (.refl _) (.refl _) writeFrame metadata)⟩
              (by omega) continuation

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedTail
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedCommit
/-! The write phase consumes the genuine staged RHS output after successful
value erasure. It uses the saved leaf and rebuilds the current mapping root,
retaining all seven compiler-generated temporary slots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceAssignmentSuccess CompatibleRenamedPlace
open ProtectedPlaceAssignmentSuccess (writtenContext)
universe u v

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

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap after : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right updatedRoot : Dynamic.Value}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {rightValue : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment store mapping world before targetHeap)
    (coreLookup : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (resolutionState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (resolutionRelated : protocol.Relates initialState resolutionState)
    (rhsResult : CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) resolution rhs node (renamed lowered ξ) environment (.value right) rhsHeap
      (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rhsPost : ProtectedStateTransition.Transition protocol resolutionState ⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩)
    (written : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator sourceTarget.selected right replacement)
      rhsHeap sourceTarget updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        (∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ))) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have setterTyped := setter_typed layout closed respects
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    obtain ⟨rhsState, rhsRelated⟩ := rhsPost
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
    obtain ⟨latest⟩ := rhsResult.latest
    cases written with
    | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
      have cellEq := sourceRead.functional latest.read
      have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
      obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
      rw [resolution.selectedEq] at applies
      obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
        CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
          (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
          (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
      have present : ∃ sourceRoot, initial = some sourceRoot := by
        cases initial with
        | some value => exact ⟨value, rfl⟩
        | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
      obtain ⟨sourceRoot, rfl⟩ := present
      have rootExists : ∃ optional rootValue,
          RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
            cell optional sourceRoot rootValue := by
        cases initialValue with
        | initialized =>
          obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
          exact ⟨_, value, root⟩
        | emptyMapping key value =>
          obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
            (layout.virtual key value cellType.symm) registryExtension
          exact ⟨_, native, root⟩
      obtain ⟨optional, rootValue, root⟩ := rootExists
      have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
      have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
          (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: actualContext)
          ambient.definitions :=
        .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
          (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
            (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
      have currentPath : PreparedPath compilation.checked source site cell.type place.projections
          0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
      have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
          currentPath sourceTarget.projections := by simpa only [cellType] using arguments
      obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
        helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
        CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
          faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
      refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
        by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
        (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
        (resolution.metadata.trans rhsResult.metadata).trans metadata,
        [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
          packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_,
        transport.extend rhsState (.refl _) extension frame metadata,
        protocol.trans (protocol.trans resolutionRelated rhsRelated)
          (transport.related rhsState (.refl _) extension frame metadata)⟩
      · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
      · intro next outputType
        rw [execute_rename layout.path closed]
        simp only [renamed_packed, Expr.rename]
        unfold execute
        simp only [packed_renamed_type]
        have snapshotEvaluated := resolution.snapshotEvaluated
        simp only [packed_renamed_type] at snapshotEvaluated
        exact (ContinuationAgreement.letE (.var coreLookup)).trans
          ((ContinuationAgreement.bind resolution.keysEvaluated).trans
            ((ContinuationAgreement.bind snapshotEvaluated).trans
              ((ContinuationAgreement.bind rhsResult.evaluated).trans
                ((ContinuationAgreement.bind modifiedEvaluated).trans
                  ((ContinuationAgreement.bind setterEvaluated).trans
                    (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten)))))))

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedFaults
/-! Pure failure phases consume the actual completed key or RHS execution.
The live root, fault token, reached diagnostic receipt, and caller transition
remain tied to that execution; no child-meaning callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedFaults
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
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
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
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
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
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
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
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
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

theorem preserves_structural {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment store mapping world before targetHeap)
    (coreLookup : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (resolutionState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (resolutionRelated : protocol.Relates initialState resolutionState)
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {rightValue : Value}
    (rhsResult : CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) resolution rhs node (renamed lowered ξ) environment (.value right) rhsHeap
      (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rhsPost : ProtectedStateTransition.Transition protocol resolutionState ⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩ reason token := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have setterTyped := setter_typed layout closed respects
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve evaluate sourceRead rootType initialValue fault
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    obtain ⟨rhsState, rhsRelated⟩ := rhsPost
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, _, modifiedEvaluated, valid⟩ :=
      CompatiblePlaceModifier.initialized_success observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, _, _⟩ :=
      CompatiblePlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
    obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
    let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata,
      reached, protocol.trans (protocol.trans resolutionRelated rhsRelated) phaseRelated,
      ⟨⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩, rhsState, sourceTarget.location, resolution.target,
        cell, optional, sourceRoot, rootValue, resolution.values, sourceTarget.projections, count, currentPath,
        protocol.trans resolutionRelated rhsRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType,
        currentArguments, fault, receipt, tree⟩⟩
    unfold execute
    simp only [packed_renamed_type]
    have snapshotEvaluated := resolution.snapshotEvaluated
    simp only [packed_renamed_type] at snapshotEvaluated
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
/-! A bare assignment runs its RHS through the same staged relation.
The native snapshot and seven-slot commit remain those emitted by the actual
compiler. Stage rejection stops before the write and retains the RHS heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {faults : RecursiveStageMeaning.FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

structure RhsResult
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
    (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : RecursiveStageMeaning.ResultRepresentsFor (payloadModel compilation.checked registry functions)
    finalMap finalWorld node.type lowered.type faults outcome value
  heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  sourcePost : ∀ right, outcome = .value right →
    Dynamic.ValueHasType context after right node.type ∧ Dynamic.HeapWellTyped context after

inductive ResultAt (operator : Syntax.ValueAssignOp) (size : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before place target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt operator size initial next output value finalStore
  | operands {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap} {current : Dynamic.Cell}
      {initialValue : Option Dynamic.Value} {selected : Option Dynamic.Value} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before place target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.value right) after)
      (currentRead : Dynamic.Heap.Reads after target.location current)
      (rootType : current.type = target.rootType)
      (initialized : Dynamic.RootInitialValue current initialValue)
      (path : Dynamic.ProjectionsRead initialValue target.projections selected)
      (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.invalidAssignmentOperands operator)) token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt operator size initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before place target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.value right) middle)
      (rightTyped : Dynamic.ValueHasType context middle right node.type)
      (middleTyped : Dynamic.HeapWellTyped context middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore)
      (post : ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, written, canonical⟩) :
      ResultAt operator size initial next output value finalStore

variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
/-- Every recursive RHS bound comes from the completed native prefix.
Only the successful branch constructs an ordinary assignment erasure for the
existing pure commit lemma; staged faults stay in the staged result. -/
theorem reflects_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {value : Value} {finalStore : Store},
      EvaluationSize child (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
        store (shift 3 (lowered.expression.rename ξ)) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt (compilation := compilation) (registry := registry) (functions := functions) (program := program) (context := context) (stages := stages) (invocation := invocation)
      (prepared := prepared) (place := place) (environment := environment) (actual := actual)
      (faults := faults) (id := id) (node := node) (actualContext := actualContext)
      protocol operator size initial (next.rename ξ) outputType value finalStore := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have bareSnapshot := (Staging.Recursive.BareTarget.of_resolves (program := program) (context := context) (evidence := invocation.evidence) (source := invocation.source) bare (snapshot.resolves bare)).2
  have phase := snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  obtain ⟨prefixSize, prefixBound, remaining⟩ := RecursiveNamedBareAssignmentContracts.snapshot_prefix_sized layout snapshot completed
  cases remaining with
  | caseLeft evaluated _ =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ :=
        rhsMeaning snapshot _ (by omega) evaluated
      cases related : result.represented with
      | fault token =>
          have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
          exact .fault bareSnapshot result.trace rfl token result.heaps result.maps result.worlds
            result.frame result.metadata rhsPost
  | caseRight evaluated retained =>
      rename_i rhsStore rightValue
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ :=
        rhsMeaning snapshot _ (by omega) evaluated
      cases related : result.represented with
      | value payload =>
          rename_i right
          rename_i rhsStore
          have rightRep : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
            .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
          obtain ⟨plain, _⟩ := ProtectedBareAssignment.rhs_of_expression snapshot protocol initial
            (faults := fun _ _ => False) (.value result.trace.sound.value_plain) result.evaluated
            (.value payload) result.heaps result.maps result.worlds result.frame result.metadata rhsPost
          obtain ⟨latest⟩ := plain.latest
          obtain ⟨initialValue, initialized⟩ := cell_initial latest.related
          rcases CompatibleBareWordModifier.modifier_total profile
            (snapshot.represented.extend result.maps result.worlds) rightRep
            (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
              ⟨invalidOperands, failed⟩ | ⟨replacement, updatedValue, replacementRep, applied, modified⟩
          · have failed : Evaluates
                (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
                (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType
                  (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
                (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
              simpa only [layout.sameType] using failed
            have evaluated := phase.wrap (LanguageResult.bind_success outputType result.evaluated
              (LanguageResult.bind_failure outputType failed))
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
            exact .operands bareSnapshot result.trace latest.read
              (latest.type.trans snapshot.type.symm) initialized .nil invalidOperands rfl
              (invalidToken _ _ invalidOperands) result.heaps result.maps result.worlds
              result.frame result.metadata rhsPost
          · have nativeModified : Evaluates
                (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
                (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType
                  (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
                (.inRight .word updatedValue) rhsStore := by
              simpa only [layout.sameType] using modified
            obtain ⟨after, commitStore, _, written, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
              commit_with_write layout snapshot bare plain rightRep replacementRep applied nativeModified actualTyped
            have terminal := (agreement .unit outputType).wrap
              (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
                (Evaluates.unit (environment := writtenEnvironment prepared.route.rootType snapshot.target .unit
                  snapshot.value rightValue updatedValue updatedValue actual) (store := commitStore)))
            obtain ⟨remainingSize, remainingBound, remaining⟩ :=
              RecursiveNamedBareAssignmentContracts.continuation_sized layout snapshot result.evaluated nativeModified
                latest.nativeRead terminal completed
            obtain ⟨rhsState, rhsRelated⟩ := rhsPost
            obtain ⟨rightTyped, middleTyped⟩ := result.sourcePost _ rfl
            exact .success bareSnapshot result.trace rightTyped middleTyped
              (.intro latest.read (latest.type.trans snapshot.type.symm) initialized (.leaf applied) written)
              finalHeaps result.maps result.worlds frame metadata
              (slots := [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
                .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed remainingBound remaining
              ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
                protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩


private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location}
    {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left)
    (second : Dynamic.Heap.Writes heap location value right) : left = right := by
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
      cases firstRead.functional secondRead
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

include transport in
theorem preserves_value_with_rhs
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {sourceSize : Nat} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace}
    (targetSnapshot : Staging.Recursive.BareTarget environment before place target)
    (sourceTrace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id (.value right) middle)
    (sourceWrite : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index)),
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize (.value right) middle value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, middle, finalStore, canonical⟩)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (invalid : Word) :
    ∃ finalStore finalMap finalWorld slots,
      Dynamic.ValueHasType context middle right node.type ∧ Dynamic.HeapWellTyped context middle ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  obtain ⟨_, sameTarget⟩ := snapshot.resolve_unique bare (targetSnapshot.resolves program context invocation.evidence invocation.source)
  subst target
  obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, rhsPost⟩ := rhsMeaning snapshot
  cases related : result.represented with
  | value payload =>
    rename_i rightValue
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
    obtain ⟨plain, _⟩ := ProtectedBareAssignment.rhs_of_expression snapshot protocol initial
      (faults := fun _ _ => False) (.value sourceTrace.sound.value_plain) result.evaluated
      (.value payload) result.heaps result.maps result.worlds result.frame result.metadata rhsPost
    cases sourceWrite with
    | intro latestRead sameType initialValue update written =>
      cases update with
      | leaf applied =>
        rcases CompatibleBareWordModifier.modifier_total profile
          (snapshot.represented.extend result.maps result.worlds) rightRep
          (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
          (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
            ⟨invalidOperands, _⟩ | ⟨replacement, updatedValue, replacementRep, generatedApply, modified⟩
        · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
        · have same := DataPlaceModifier.assignment_functional generatedApply applied
          subst replacement
          obtain ⟨generatedHeap, finalStore, _, generatedWrite, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
            commit_with_write layout snapshot bare plain rightRep replacementRep applied
              (by simpa only [layout.sameType] using modified) actualTyped
          have same := writes_functional generatedWrite written
          subst generatedHeap
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          exact ⟨finalStore, rhsMap, rhsWorld,
            [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
              .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target],
            (result.sourcePost _ rfl).1, (result.sourcePost _ rfl).2,
            finalHeaps, result.maps, result.worlds, frame, metadata, rfl, typed,
            ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
              protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩,
            agreement⟩

theorem preserves_fault_with_rhs
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared)
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index)),
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize (.fault failure) after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (next : Expr) (output : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, result, post⟩ := rhsMeaning snapshot
  cases result.represented with
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      (snapshot_prefix layout snapshot lowered.expression next output
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid).wrap
        (LanguageResult.bind_failure output result.evaluated),
      matched, result.heaps, result.maps, result.worlds, result.frame, result.metadata, post⟩

theorem preserves_operands_with_rhs
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {sourceSize : Nat} {right : Dynamic.Value} {after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (targetSnapshot : Staging.Recursive.BareTarget environment before place target)
    (invalidOperands : Dynamic.AssignmentOperandsInvalid operator target.selected right)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index)),
      ∃ value finalStore finalMap finalWorld,
        RhsResult (program := program) (context := context) (stages := stages) (invocation := invocation)
          (faults := faults) (id := id) (node := node) (lowered := lowered)
          snapshot sourceSize (.value right) after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (next : Expr) (output : Ty) (invalid : Word)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft output (.word token)) finalStore ∧ faults (.semantic (.invalidAssignmentOperands operator)) token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  obtain ⟨_, sameTarget⟩ := snapshot.resolve_unique bare (targetSnapshot.resolves program context invocation.evidence invocation.source)
  subst target
  obtain ⟨value, rhsStore, rhsMap, rhsWorld, result, post⟩ := rhsMeaning snapshot
  cases result.represented with
  | value payload =>
    rename_i rightValue
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
    rcases CompatibleBareWordModifier.modifier_total profile
      (snapshot.represented.extend result.maps result.worlds) rightRep
      (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
      (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
        ⟨_, failed⟩ | ⟨_, _, _, applied, _⟩
    · have failed : Evaluates
          (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
          (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType
            (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
          (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
        simpa only [layout.sameType] using failed
      exact ⟨invalid, rhsStore, rhsMap, rhsWorld,
        (snapshot_prefix layout snapshot lowered.expression next output
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid).wrap
          (LanguageResult.bind_success output result.evaluated (LanguageResult.bind_failure output failed)),
        invalidToken _ _ invalidOperands, result.heaps, result.maps, result.worlds, result.frame, result.metadata, post⟩
    · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
end
