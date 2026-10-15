import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedFaults

/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatiblePlaceResolution.Execution values.checked registry functions prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)


/-- Only an actual successful staged RHS is erased to the ordinary suffix
receipt. Its current root is read from the actual represented RHS heap. -/
theorem RhsResult.to_ordinary_value {size : Nat} {right : Dynamic.Value} {after : Dynamic.Heap}
    {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : RhsResult (values := values) (program := program) (context := context) (stages := stages)
      (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
      (environment := environment) resolution size (.value right) after native finalStore finalMap finalWorld) :
    CompatiblePlaceRhs.Result (program := program) (context := context)
      (evidence := invocation.evidence) (source := invocation.source)
      (faults := fun reason token => faults (.semantic reason) token)
      resolution id node (renamed lowered ξ) environment (.value right) after native finalStore finalMap finalWorld := by
  refine ⟨.value result.trace.sound.value_plain, result.evaluated, ?_, result.heaps,
    result.maps, result.worlds, result.frame, result.metadata, ?_⟩
  · cases result.represented with
    | value related => exact .value related
  · obtain ⟨cell, read, sameType, _⟩ := result.metadata _ _ resolution.currentRead
    have reference := resolution.reference.extend result.maps result.worlds
    obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at result.heaps reference read
    exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩
end Rhs

section Resolution
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {scope : Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrative actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before getter : Dynamic.Heap} {store : Store} {index : Nat}
  {target : Dynamic.ResolvedPlace} {sources : List Dynamic.Value}

/-- The independent ordered key trace determines the getter state before any
RHS execution. The original key value types and deep heap typing are retained. -/
theorem preserves_keys (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection}
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (ordered : Staging.Recursive.ProjectedTarget.Values place.projections sources resolved) :
    ∃ execution : CompatiblePlaceTargetKeys.Execution values.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved actual before getter store mapping world (ξ index),
      Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧ Dynamic.HeapWellTyped context getter ∧
      ∃ reached : callerProtocol.State ⟨scope, execution.keyMap, execution.keyWorld, getter, execution.keyStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
    maps, worlds, frame, metadata, typed, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.preserves_values bridge budget
      layout.children unique originalKeyTyped meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) initial admitted
      (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
  obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyEq⟩ := writable.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases initialRead.functional staticRead
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ initialRead
  refine ⟨⟨target, sources, native, keyStore, keyMap, keyWorld, cell, read,
    sameType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected,
    ordered.to_data, ?_, ?_, keyHeaps, maps, worlds, frame, metadata⟩,
    typed, post.at_values.heap, reached, related, post.at_values⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · simpa only [renamedCodes_types] using represented

theorem preserves_resolution (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations values.checked.catalog functions identities)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter place sources target) :
    ∃ resolution : CompatiblePlaceResolution.Execution values.checked registry functions prepared
      (renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before getter,
      resolution.sources = sources ∧ Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧
      Dynamic.HeapWellTyped context getter ∧
      actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) ∧
      ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, getter, resolution.store, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related⟩ :=
    ProtectedStagedProjectedResolution.preserves layout.path layout.views layout.keyTypes layout.leafProjected
      layout.virtual extension layout.nonempty
      (CompatibleRenamedPlace.getter_typed layout (CompatibleRenamedPlace.virtual_closed layout ordinary)
        (CompatibleRenamedPlace.environment_respects environments.runtime_hasTypes actualTyped agrees))
      callerProtocol transport faithful observations environments locals agrees actualTyped initial
      (fun target _ hiddenTyped => by
        obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
          maps, worlds, frame, metadata, typed, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.preserves_values bridge budget
            layout.children unique originalKeyTyped meaning environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
        exact ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps, maps, worlds,
          frame, metadata, typed, post.at_values.heap, reached, related⟩)
      slot writable snapshot
  exact ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related, keyHeap,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows resolution.frame⟩
end Resolution

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
theorem preserves_value (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {getter middle after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) middle)
    (rhsBound : rhsSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyTyped := tree_typed layout.children unique originalKeyTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | value payload =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      obtain ⟨updatedValue, finalStore, finalMap, finalWorld, _root, finalHeaps, maps, worlds, frame, metadata,
          slots, count, typed, agreement, reached, related⟩ :=
        ProtectedStagedProjectedCommit.preserves layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments heaps agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost write invalid
      refine ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata,
        count, ?_, ⟨reached, related, ?_, ?_⟩, agreement⟩
      · simpa only [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext,
          ProtectedPlaceAssignmentSuccess.writtenContext] using typed
      · exact CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTyped)
          keyValues keyHeap resolution.metadata snapshot (rhsResult.sourcePost _ rfl).2
          (rhsResult.sourcePost _ rfl).1 rhsResult.metadata write
      · exact StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame

include environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected in
/-- A failed key row stops before the getter and RHS. -/
theorem preserves_key_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
    (bounded : keySize ≤ budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases ready with
    | intro lookup read =>
      obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge budget layout.children unique originalKeyTyped
          meaning environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          (.cons (.cellRef reference.typed) actualTyped) initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace) bounded
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post.rows⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      apply Evaluates.letE (.var (agrees selected))
      apply LanguageResult.bind_failure
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- A successful key row and getter precede the actual staged RHS fault. -/
theorem preserves_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {failure : Staging.Recursive.Failure} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.fault failure) after)
    (rhsBound : rhsSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsState, rhsRelated⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | fault matched =>
      refine ⟨_, rhsStore, rhsMap, rhsWorld, ?_, matched, rhsResult.heaps,
        resolution.maps.trans rhsResult.maps, resolution.worlds.trans rhsResult.worlds,
        resolution.frame.trans rhsResult.frame, resolution.metadata.trans rhsResult.metadata,
        rhsState, callerProtocol.trans resolutionRelated rhsRelated,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool rhsState) admitted.rows (resolution.frame.trans rhsResult.frame)⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      have snapshotEvaluated := resolution.snapshotEvaluated
      simp only [packed_renamed_type] at snapshotEvaluated
      exact .letE (.var coreLookup) (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated (LanguageResult.bind_failure _ rhsResult.evaluated)))


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- Getter faults preserve the original reached diagnostic witness. -/
theorem preserves_getter_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
    (bounded : keySize ≤ budget)
    (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases failed with
    | dangling lookup initialRead ordered absent =>
      obtain ⟨execution, _, _, reached, related, post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      exact (absent.excludes_read execution.read).elim
    | projection lookup initialRead ordered currentRead initialValue fault =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
          evaluated, finalHeaps, maps, worlds, frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedFaults.preserves_projection layout ordinary callerProtocol transport
          environments agrees actualTyped initial execution ⟨keyState, keyRelated⟩ lookup initialRead
          (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead extension faithful observations
          initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated
    | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      obtain ⟨finalStore, finalMap, finalWorld, _sourceFault, evaluated, finalHeaps, maps, worlds,
          frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedFaults.preserves_uninitialized layout callerProtocol initial execution ⟨keyState, keyRelated⟩
          lookup initialRead (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead
          ordinary empty notMapping nonempty operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
      refine ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, ?_, uninitialized reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- Structural write failure is checked against the latest root after the
successful RHS. Represented initialized scalar operands cannot create an
additional operand fault in this projected profile. -/
theorem preserves_write_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {right : Dynamic.Value} {reason : Dynamic.SemanticFault} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) after)
    (rhsBound : rhsSize < budget)
    (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | @value _ native rightRep =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      cases failed with
      | operands read rootType initialValue pathRead invalidOperands =>
        have rightRep : ValueRep values.checked registry functions rhsMap rhsWorld leaf right native prepared.route.leafType :=
          .compatible rightView (by simpa only [payloadModel, renamed, rightType] using rightRep)
        obtain ⟨replacement, replacementValue, replacementRep, applies, evaluated, valid⟩ :=
          CompatiblePlaceModifier.initialized_success observations profile ordinaryRhs.saved_snapshot rightRep
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) native actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
        rw [resolution.selectedEq] at invalidOperands
        exact (valid invalidOperands).elim
      | structural read rootType initialValue fault =>
        obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
            evaluated, finalHeaps, maps, worlds, frame, metadata, reached, related, diagnostic⟩ :=
          ProtectedStagedProjectedFaults.preserves_structural layout ordinary extension callerProtocol transport faithful observations
            generated found rightView rightType profile environments agrees actualTyped initial resolution coreLookup
            resolutionState resolutionRelated ordinaryRhs rhsPost
            (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)) trace.sound.value_plain
            read rootType initialValue fault (next.rename ξ) output invalid
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
          finalHeaps, maps, worlds, frame, metadata, reached, related,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
        change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
          next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
        simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
