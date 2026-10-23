import Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentResolution
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedFaults

/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
theorem preserves_value (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
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
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) compiled.indexed.layouts.definitions ∧
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
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
          (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
    cases represented : rhsResult.represented with
    | value payload =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      obtain ⟨updatedValue, finalStore, finalMap, finalWorld, _root, finalHeaps, maps, worlds, frame, metadata, effect,
          slots, count, typed, agreement, reached, related⟩ :=
        CellAwareStagedProjectedCommit.preserves GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments heaps agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost write invalid
      refine ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect,
        count, ?_, ⟨reached, related, ?_, ?_⟩, agreement⟩
      · simpa only [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext,
          ProtectedPlaceAssignmentSuccess.writtenContext, CallableIndexedAmbient.ambientDefinitions] using typed
      · exact CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTyped)
          keyValues keyHeap resolution.metadata snapshot (rhsResult.sourcePost _ rfl).2
          (rhsResult.sourcePost _ rfl).1 rhsResult.metadata write
      · exact StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected in
/-- A failed key row stops before the getter and RHS. -/
theorem preserves_key_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    {keySize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
    (bounded : keySize ≤ budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
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
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        CellAwareInvocationExpressionSequence.preserves_fault bridge budget layout.children unique originalKeyTyped
          meaning environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          (.cons (.cellRef reference.typed) actualTyped) initial admitted authority physical owner ownerFrame
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace) bounded
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, effect,
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

include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- A successful key row and getter precede the actual staged RHS fault. -/
theorem preserves_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
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
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
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
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsState, rhsRelated⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
          (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
    cases represented : rhsResult.represented with
    | fault matched =>
      refine ⟨_, rhsStore, rhsMap, rhsWorld, ?_, matched, rhsResult.heaps,
        resolution.maps.trans rhsResult.maps, resolution.worlds.trans rhsResult.worlds,
        resolution.frame.trans rhsResult.frame, resolution.metadata.trans rhsResult.metadata,
        resolution.effect.trans rhsResult.effect,
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


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- Getter faults preserve the original reached diagnostic witness. -/
theorem preserves_getter_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
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
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  obtain ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩ :=
    PreparedProjectedDiagnosticFields.projected errors projected
  obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  cases failed with
  | dangling lookup initialRead ordered absent =>
    obtain ⟨execution, _, _, reached, related, post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    exact (absent.excludes_read execution.read).elim
  | projection lookup initialRead ordered currentRead initialValue fault =>
    obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
        evaluated, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, diagnostic⟩ :=
      CellAwareStagedProjectedFaults.preserves_projection GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary callerProtocol transport
        environments agrees actualTyped initial execution ⟨keyState, keyRelated⟩ lookup initialRead
        (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead extension faithful observations
        initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
    refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
    change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
      next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
    simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated
  | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
    obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable trace bounded lookup initialRead ordered
    obtain ⟨finalStore, finalMap, finalWorld, _sourceFault, evaluated, finalHeaps, maps, worlds,
        frame, metadata, effect, reached, related, diagnostic⟩ :=
      CellAwareStagedProjectedFaults.preserves_uninitialized GeneralizedLocalDescriptorHeap.ordinary_cells layout callerProtocol initial execution ⟨keyState, keyRelated⟩
        lookup initialRead (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead
        ordinary empty notMapping nonempty operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
    refine ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, ?_, uninitialized reached related diagnostic,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
    change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
      next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
    simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated


include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected faithful observations in
/-- Structural write failure is checked against the latest root after the
successful RHS. Represented initialized scalar operands cannot create an
additional operand fault in this projected profile. -/
theorem preserves_write_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
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
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  obtain ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩ :=
    PreparedProjectedDiagnosticFields.projected errors projected
  have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
  obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
    preserves_resolution bridge budget layout ordinary extension transport faithful observations
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique originalKeyTyped meaning
      slot writable keyTrace keyBound snapshot
  obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
    rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
      (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      agrees actualTyped resolutionState resolutionAdmission (authority.transport resolution.effect)
        (physical.transport resolution.effect resolution.frame) owner ownerFrame trace
  cases represented : rhsResult.represented with
  | @value _ native rightRep =>
    have ordinaryRhs := rhsResult.to_ordinary_value
    cases failed with
    | operands read rootType initialValue pathRead invalidOperands =>
      have rightRep : ValueRep compiled.compatible.checked registry functions rhsMap rhsWorld leaf right native prepared.route.leafType :=
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
          evaluated, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, diagnostic⟩ :=
        CellAwareStagedProjectedFaults.preserves_structural GeneralizedLocalDescriptorHeap.ordinary_cells layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost
          (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)) trace.sound.value_plain
          read rootType initialValue fault (next.rename ξ) output invalid
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentHeads
