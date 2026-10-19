import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.GenericProjectedBitNotPreparedOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults

/-! The actual staged key row produces the unary write and its reached admission.
Getter faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
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
  {assignment : AssignmentResolution}
  (head : CompatibleProjectedBitNotStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment)
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
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
theorem preserves_value (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize : Nat} {sources : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      getter target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped word =>
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed head.layout.children unique originalKeyTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, _resolutionAdmission⟩ :=
      CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_resolution bridge budget head.layout head.ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        head.slot head.writable keyTrace keyBound snapshot
    obtain ⟨commit, typed, reached, related⟩ :=
      ProtectedStagedProjectedBitNotCommit.of_write head.layout head.ordinary extension callerProtocol transport faithful observations
        head.profile environments agrees actualTyped resolution initial resolutionState resolutionRelated write
        (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld,
      [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target],
      commit.heaps, resolution.maps, resolution.worlds.trans commit.worlds,
      resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata, rfl, typed,
      ⟨reached, related, ?_, ?_⟩, ?_⟩
    · exact CallableIndexedOwnedStagedProjectedBitNotAdmission.heap_after_bitNot unique (.intro targetTyped word)
        locals (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTyped)
        keyValues keyHeap resolution.metadata snapshot write
    · exact StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows
        (resolution.frame.trans commit.frame)
    · intro next output
      change ContinuationAgreement actual store
        ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
          next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _ _
      rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)]
      simpa only [renamed_packed, Expr.rename, LanguageResult.success, writtenEnvironment, modifiedEnvironment, rhsEnvironment, snapshotEnvironment, keysEnvironment, referenceEnvironment, List.cons_append, List.nil_append] using
        commit.prefix_agreement resolution coreLookup (next.rename ξ) output

include environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected in
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
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped _ =>
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases ready with
    | intro lookup read =>
      obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup head.slot
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge budget head.layout.children unique originalKeyTyped
          meaning environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType head.prepared.route.rootType) target])
          (.cons (.cellRef reference.typed) actualTyped) initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace) bounded
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post.rows⟩
      change Evaluates actual store ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _
      rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)]
      simp only [renamed_packed, Expr.rename, LanguageResult.success]
      unfold execute
      simp only [packed_renamed_type]
      apply Evaluates.letE (.var (agrees selected))
      apply LanguageResult.bind_failure
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
theorem preserves_getter_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (errors : head.ReachedErrors functions callerProtocol environment initial (fun reason token => faults (.semantic reason) token) (registry := registry))
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
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped _ =>
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases failed with
    | dangling lookup initialRead ordered absent =>
      obtain ⟨execution, _, _, reached, related, post⟩ := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_keys bridge budget head.layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        head.slot head.writable trace bounded lookup initialRead ordered
      exact (absent.excludes_read execution.read).elim
    | projection lookup initialRead ordered currentRead initialValue fault =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_keys bridge budget head.layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        head.slot head.writable trace bounded lookup initialRead ordered
      obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
          evaluated, finalHeaps, maps, worlds, frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedBitNotFaults.preserves_projection head.layout head.ordinary callerProtocol transport
          environments agrees actualTyped initial execution ⟨keyState, keyRelated⟩ lookup initialRead
          (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead extension faithful observations
          initialValue fault (next.rename ξ) output head.invalid
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, errors.missing reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _
      simpa only [execute_rename head.layout.path (virtual_closed head.layout head.ordinary), renamed_packed, Expr.rename, LanguageResult.success] using evaluated
    | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_keys bridge budget head.layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        head.slot head.writable trace bounded lookup initialRead ordered
      obtain ⟨finalStore, finalMap, finalWorld, _sourceFault, evaluated, finalHeaps, maps, worlds,
          frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedBitNotFaults.preserves_uninitialized head.layout callerProtocol initial execution ⟨keyState, keyRelated⟩
          lookup initialRead (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead
          head.ordinary empty notMapping nonempty (next.rename ξ) output head.invalid
      refine ⟨head.prepared.invalidProjection, finalStore, finalMap, finalWorld, ?_, errors.uninitialized reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _
      simpa only [execute_rename head.layout.path (virtual_closed head.layout head.ordinary), renamed_packed, Expr.rename, LanguageResult.success] using evaluated

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
