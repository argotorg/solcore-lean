import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StagedProjectedBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReceiptOperations
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.Staging.RecursiveBareBitNot
import Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaders

/-!
# Admitted staged profile: for loops

`for` heads, edges, sequences and iterations, initializer sources by form, and projected bit-not updates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
/-! Projected unary heads retain the actual key row, snapshot, write and reached caller.
The Unit temporary is administrative and has no Source RHS trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)


inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | keyFault {keySize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | getterFault {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | success {keySize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        targetHeap target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotPreservation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotReflection
/-! Completed native unary writes reconstruct the staged key row and saved snapshot.
The typed numeric snapshot supplies the actual independent Source write. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
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

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : head.ReachedErrors functions callerProtocol environment initial (fun reason token => faults (.semantic reason) token) (registry := registry))
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped word =>
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyRow : ExpressionsHaveTypes invocation.source context
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) head.sourceTypes := by
      simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed head.layout.children unique keyTyped
    have nativeCompleted := completed
    change EvaluationSize size actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit) next output
        (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) value finalStore at nativeCompleted
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)] at nativeCompleted
    simp only [renamed_packed, Expr.rename, LanguageResult.success] at nativeCompleted
    have prefixResult := ProtectedStagedProjectedPrefix.reflects_getter budget head.layout head.ordinary extension
      callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial errors.missing errors.uninitialized
      (by
        intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
            frame, metadata, typedValues, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.reflects bridge budget head.layout.children unique keyTyped
            boundedReflection environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType head.prepared.route.rootType) target])
            hiddenTyped initial admitted evaluated smaller
        refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
          frame, metadata, ?_, reached, related⟩
        · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
        · intro sources same
          exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
      head.slot head.writable nativeCompleted bounded
    cases prefixResult with
    | keyFault ready trace same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .keyFault ready trace same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | getterFault trace failed same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .getterFault trace failed same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | resolved resolution keyTrace snapshot keyValues getterHeap prefixBound remaining prefixPost =>
      obtain ⟨getterState, getterRelated⟩ := prefixPost
      obtain ⟨replacement, native, represented, applies, _, _⟩ :=
        CompatiblePlaceNumericBitNotModifier.success head.profile resolution.snapshotRelated
          (environment := rhsEnvironment head.prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) .unit actual) (rhs := .var 0) (.var (index := 1) rfl)
          (binaryOperator (head.prepared.route.leafType = .integer) .equal) resolution.store head.invalid
      have applies := resolution.selectedEq.symm ▸ applies
      have sourceTrace := snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)
      obtain ⟨updated, after, write⟩ := CompatiblePlaceBitNotModifier.write_exists sourceTrace applies
      obtain ⟨commit, typed, reached, related⟩ :=
        ProtectedStagedProjectedBitNotCommit.of_write head.layout head.ordinary extension callerProtocol transport faithful observations
          head.profile environments agrees actualTyped resolution initial getterState getterRelated write
          (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
      obtain ⟨remainingSize, strict, continuation⟩ := commit.reflects_size remaining
      exact .success keyTrace snapshot write commit.heaps resolution.maps
        (resolution.worlds.trans commit.worlds) (resolution.frame.trans commit.frame)
        (resolution.metadata.trans commit.metadata)
        (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
          packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target])
        rfl typed reached related
        ⟨CallableIndexedOwnedStagedProjectedBitNotAdmission.heap_after_bitNot unique (.intro targetTyped word)
          locals keyRow keyValues getterHeap resolution.metadata snapshot write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows
            (resolution.frame.trans commit.frame)⟩
        (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
/-! Actual for initializers stay live through the loop. Returning to the
surrounding statements restores only their outer lexical bindings. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

inductive Trace (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Nat → Staging.Recursive.BodyOutcome → Dynamic.Heap → Prop where
  | initializerFault {initialSize finalContext failure after}
      (initial : Staging.Recursive.Size.ForItems program stages initialSize invocation context environment before
        items finalContext (.fault failure) after) :
      Trace program stages invocation context environment before items test post statements
        (Staging.Recursive.Size.stepSize [initialSize]) (.fault failure) after
  | loop {initialSize loopSize loopContext loopEnvironment middle outcome after}
      (initial : Staging.Recursive.Size.ForItems program stages initialSize invocation context environment before
        items loopContext (.done loopEnvironment) middle)
      (executed : Staging.Recursive.Size.ForLoop program stages loopSize invocation loopContext loopEnvironment middle
        test post statements outcome after) :
      Trace program stages invocation context environment before items test post statements
        (Staging.Recursive.Size.stepSize [initialSize, loopSize]) (outcome.restore environment) after

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- The actual initializer prefix and loop return to the original outer context.
Their Source traces retain the loop entry context and exact intermediate heap. -/
def Reflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program stages invocation context environment before items test post statements sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Source initialization and loop execution retain the reached heap and restore
admission at the outer context before subsequent statements. -/
def Preserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap},
      Trace program stages invocation context environment before items test post statements size outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
/-! A compiler initializer prefix contributes its actual item trace to the
same finite for head. Binder scopes restore only lexical bindings; all grades,
heap effects and both failure tags remain those of the executed prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context nextContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before middle bound written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size childSize : Nat} {outcome : BodyOutcome}

private theorem restore_twice (outcome : BodyOutcome) (inner outer : Dynamic.Environment) :
    (outcome.restore inner).restore outer = outcome.restore outer := by
  cases outcome <;> rfl

private theorem grade_absent (initial loop : Nat) :
    Size.stepSize [Size.stepSize [initial], loop] = Size.stepSize [Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

private theorem grade_prefix (child initial loop : Nat) :
    Size.stepSize [Size.stepSize [child, initial], loop] = Size.stepSize [child, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

/-- An actual uninitialized header allocation remains live through the rest
of initialization and the loop; the whole head restores the outer bindings. -/
theorem prepend_absent {binder : TypedBinder} {location : Dynamic.Location}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound)
    (next : Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
      items test post body size outcome after) :
    Trace program stages invocation context environment before (.letDecl binder none :: items) test post body
      (Size.stepSize [size]) (outcome.restore environment) after := by
  cases next with
  | initializerFault initial => exact .initializerFault (.absent mono extended allocated initial)
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initial loop =>
      simpa only [grade_absent, restore_twice] using
        (Trace.loop (Size.ForItems.absent mono extended allocated initial) loop)

theorem prepend_initialized {binder : TypedBinder} {initializer : ExpressionId}
    {value : Dynamic.Value} {location : Dynamic.Location}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Size.Expression program stages childSize invocation context environment before initializer (.value value) middle)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound)
    (next : Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
      items test post body size outcome after) :
    Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body
      (Size.stepSize [childSize, size]) (outcome.restore environment) after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.initialized mono extended child allocated initial))
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initial loop =>
      simpa only [grade_prefix, restore_twice] using
        (Trace.loop (Size.ForItems.initialized mono extended child allocated initial) loop)

theorem prepend_expression {id : ExpressionId} {value : Dynamic.Value}
    (child : Size.Expression program stages childSize invocation context environment before id (.value value) middle)
    (next : Trace program stages invocation context environment middle items test post body size outcome after) :
    Trace program stages invocation context environment before (.expression id :: items) test post body
      (Size.stepSize [childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.expression child initial))
  | loop initial loop => simpa only [grade_prefix] using (Trace.loop (Size.ForItems.expression child initial) loop)

theorem prepend_assignment {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {value updated : Dynamic.Value} {target : Dynamic.ResolvedPlace}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.value value) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
      middle target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.assignment snapshot child write initial))
  | loop initial loop => simpa only [grade_prefix] using (Trace.loop (Size.ForItems.assignment snapshot child write initial) loop)

theorem initializer_fault {binder : TypedBinder} {initializer : ExpressionId} {failure : Failure}
    (mono : binder.scheme.quantified = [])
    (child : Size.Expression program stages childSize invocation context environment before initializer (.fault failure) after) :
    Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.initializerFault mono child)

theorem expression_fault {id : ExpressionId} {failure : Failure}
    (child : Size.Expression program stages childSize invocation context environment before id (.fault failure) after) :
    Trace program stages invocation context environment before (.expression id :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.expressionFailure child)

theorem assignment_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {failure : Failure}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.assignmentFailure snapshot child)

theorem assignment_operands {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {right : Dynamic.Value} {currentCell : Dynamic.Cell}
    {initial currentSelected : Option Dynamic.Value}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.value right) after)
    (currentRead : Dynamic.Heap.Reads after target.location currentCell)
    (rootType : currentCell.type = target.rootType)
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (pathRead : Dynamic.ProjectionsRead initial target.projections currentSelected)
    (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault (.semantic (.invalidAssignmentOperands operator))) after :=
  .initializerFault (.assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid)

/-- Empty initialization contributes its genuine empty-items grade. -/
theorem nil
    (trace : Trace program stages invocation context environment before [] test post body size outcome after) :
    ∃ loopSize rawOutcome,
      size = Size.stepSize [Size.stepSize [], loopSize] ∧ outcome = rawOutcome.restore environment ∧
      Size.ForLoop program stages loopSize invocation context environment before test post body rawOutcome after := by
  cases trace with
  | initializerFault initial => cases initial
  | loop initial loop =>
      cases initial
      exact ⟨_, _, rfl, rfl, loop⟩

theorem absent {binder : TypedBinder}
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Trace program stages invocation context environment before (.letDecl binder none :: items) test post body size outcome after) :
    ∃ nextSize location bound nextOutcome,
      size = Size.stepSize [nextSize] ∧ outcome = nextOutcome.restore environment ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
        items test post body nextSize nextOutcome after := by
  cases trace with
  | initializerFault initial =>
      obtain ⟨tailSize, location, bound, rfl, allocated, next⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended initial
      exact ⟨_, location, bound, _, rfl, rfl, allocated, .initializerFault next⟩
  | loop initial loop =>
      obtain ⟨tailSize, location, bound, rfl, allocated, next⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended initial
      exact ⟨_, location, bound, _, grade_absent _ _, (restore_twice _ _ _).symm, allocated, .loop next loop⟩

theorem initialized {binder : TypedBinder} {initializer : ExpressionId}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before initializer (.fault failure) after) ∨
    (∃ childSize nextSize value location middle bound nextOutcome,
      size = Size.stepSize [childSize, nextSize] ∧ outcome = nextOutcome.restore environment ∧
      Size.Expression program stages childSize invocation context environment before initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
        items test post body nextSize nextOutcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized monomorphic extended initial with failed | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, tailSize, value, location, middle, bound, rfl, child, allocated, next⟩ := continued
        refine .inr ⟨_, _, _, _, _, _, _, ?_, rfl, child, allocated, .initializerFault next⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized monomorphic extended initial with failed | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨childSize, tailSize, value, location, middle, bound, rfl, child, allocated, next⟩ := continued
        exact .inr ⟨_, _, _, _, _, _, _, grade_prefix _ _ _, (restore_twice _ _ _).symm,
          child, allocated, .loop next loop⟩

theorem expression {id : ExpressionId}
    (trace : Trace program stages invocation context environment before (.expression id :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before id (.fault failure) after) ∨
    (∃ childSize nextSize value middle,
      size = Size.stepSize [childSize, nextSize] ∧
      Size.Expression program stages childSize invocation context environment before id (.value value) middle ∧
      Trace program stages invocation context environment middle items test post body nextSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression initial with failed | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, tailSize, value, middle, rfl, child, next⟩ := continued
        refine .inr ⟨_, _, _, _, ?_, child, .initializerFault next⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression initial with failed | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨childSize, tailSize, value, middle, rfl, child, next⟩ := continued
        exact .inr ⟨_, _, _, _, grade_prefix _ _ _, child, .loop next loop⟩

theorem assignment {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {target : Dynamic.ResolvedPlace}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize right currentCell initial currentSelected,
      size = Size.stepSize [Size.stepSize [childSize]] ∧
      outcome = .fault (.semantic (.invalidAssignmentOperands operator)) ∧
      Size.Expression program stages childSize invocation context environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ childSize nextSize value middle written updated,
      size = Size.stepSize [childSize, nextSize] ∧
      Size.Expression program stages childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      Trace program stages invocation context environment written items test post body nextSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot initial with failed | invalid | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, right, currentCell, initial, currentSelected, rfl, _, same,
          child, currentRead, rootType, initialValue, pathRead, operands⟩ := invalid
        cases same
        exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, child, currentRead, rootType, initialValue, pathRead, operands⟩)
      · obtain ⟨childSize, tailSize, value, middle, written, updated, rfl, child, write, next⟩ := continued
        refine .inr (.inr ⟨_, _, _, _, _, _, ?_, child, write, .initializerFault next⟩)
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot initial with failed | invalid | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨_, _, _, _, _, _, _, same, _⟩ := invalid
        cases same
      · obtain ⟨childSize, tailSize, value, middle, written, updated, rfl, child, write, next⟩ := continued
        exact .inr (.inr ⟨_, _, _, _, _, _, grade_prefix _ _ _, child, write, .loop next loop⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotSource
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before targetHeap written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size keysSize : Nat} {outcome : BodyOutcome}
  {assignment : AssignmentResolution}
  {values : List Dynamic.Value} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
  {reason : Dynamic.SemanticFault} {failure : Failure}

private theorem projected_bitNot_grade (keys initial loop : Nat) :
    Size.stepSize [Size.stepSize [keys, initial], loop] =
      Size.stepSize [keys, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

theorem prepend_projected_bitNot
    (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      targetHeap target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [keysSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.projectedBitNot projected keys snapshot write initial))
  | loop initial loop =>
      simpa only [projected_bitNot_grade] using
        (Trace.loop (Size.ForItems.projectedBitNot projected keys snapshot write initial) loop)

theorem projected_bitNot_root_fault (projected : assignment.target.projections ≠ [])
    (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.projectedBitNotRootFault projected failed)

theorem projected_bitNot_keys_fault (projected : assignment.target.projections ≠ [])
    (ready : ProjectedTarget.RootReady environment before assignment.target)
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after :=
  .initializerFault (.projectedBitNotKeysFault projected ready keys)

theorem projected_bitNot_getter_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) after)
    (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedBitNotGetterFault projected keys failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedSource
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before targetHeap middle written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size keysSize childSize : Nat} {outcome : BodyOutcome}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {values : List Dynamic.Value} {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
  {reason : Dynamic.SemanticFault} {failure : Failure}

private theorem projected_grade (keys child initial loop : Nat) :
    Size.stepSize [Size.stepSize [keys, child, initial], loop] =
      Size.stepSize [keys, child, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

theorem prepend_projected_assignment
    (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [keysSize, childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.projectedAssignment projected keys snapshot child write initial))
  | loop initial loop =>
      simpa only [projected_grade] using
        (Trace.loop (Size.ForItems.projectedAssignment projected keys snapshot child write initial) loop)

theorem projected_root_fault (projected : assignment.target.projections ≠ [])
    (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.projectedAssignmentRootFault projected failed)

theorem projected_keys_fault (projected : assignment.target.projections ≠ [])
    (ready : ProjectedTarget.RootReady environment before assignment.target)
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after :=
  .initializerFault (.projectedAssignmentKeysFault projected ready keys)

theorem projected_getter_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) after)
    (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedAssignmentGetterFault projected keys failed)

theorem projected_rhs_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault failure) after :=
  .initializerFault (.projectedAssignmentRhsFault projected keys snapshot child)

theorem projected_write_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.value right) after)
    (failed : ProjectedTarget.WriteFault operator target right after reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedAssignmentWriteFault projected keys snapshot child failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotSource
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem prepend_bitNot {assignment : AssignmentResolution} {target : Dynamic.ResolvedPlace}
    {updated : Dynamic.Value}
    (snapshot : BareTarget environment before assignment.target target)
    (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      before target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [size]) outcome after := by
  cases next with
  | initializerFault initial => exact .initializerFault (.bitNot snapshot write initial)
  | loop initial loop =>
      have grade (initial loop : Nat) : Size.stepSize [Size.stepSize [initial], loop] =
          Size.stepSize [Size.stepSize [initial, loop]] := by
        simp [Size.stepSize]
        omega
      simpa only [grade] using (Trace.loop (Size.ForItems.bitNot snapshot write initial) loop)

theorem bitNot_fault {assignment : AssignmentResolution} {reason : Dynamic.SemanticFault}
    (bare : assignment.target.projections = [])
    (failed : Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
      environment before assignment.target reason before) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.bitNotFault bare failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
/-! Bare unary heads retain the actual caller state and exact written heap.
The operation has no expression child; its native continuation still supplies
its genuine strict evaluation bound. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (faults : FunctionCalls.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
        environment before assignment.target reason before)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld before finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | success {remainingSize : Nat} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
      {after : Dynamic.Heap} {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore

variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} (head : CompatibleBitNotStatements.Head context scope assignment)
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
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)

include transport environments heaps locals agrees actualTyped initial admitted assignmentTyped in
theorem reflects_bounded (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) :
    ResultAt bridge size values.checked registry functions context invocation faults scope
      (head.writtenContext actualContext) assignment environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore := by
  rcases head.reflects_sized (source := invocation.source) functions program invocation.evidence environments heaps locals agrees actualTyped errors completed with failed | succeeded
  · obtain ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, same, matched, finalHeaps,
      maps, worlds, frame, metadata⟩ := failed
    have trace := trace.sound
    cases Staging.Recursive.bitNot_fault_heap head.bare trace
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      callerProtocol transport initial maps worlds frame metadata
    exact .fault trace same matched finalHeaps maps worlds frame reached related
      (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
  · obtain ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize,
      trace, finalHeaps, maps, worlds, frame, metadata, count, typed, bounded, remaining⟩ := succeeded
    cases trace.sound with
    | intro resolved write =>
      obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves head.bare resolved
      obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
        callerProtocol transport initial maps worlds frame metadata
      exact .success snapshot write finalHeaps maps worlds frame metadata count typed reached related
        ⟨(Staging.Recursive.SelectedPreservation.bare_write_bitNot locals admitted.heap assignmentTyped snapshot write).1,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩ bounded remaining

include transport environments heaps locals agrees actualTyped initial admitted assignmentTyped in
theorem preserves_value {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value} {after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      before target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, agreement⟩ :=
    head.preserves_prefix functions program invocation.evidence environments heaps locals agrees actualTyped
      (.intro (snapshot.resolves program context invocation.evidence invocation.source) write)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    callerProtocol transport initial maps worlds frame metadata
  exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed,
    ⟨reached, related,
      (Staging.Recursive.SelectedPreservation.bare_write_bitNot locals admitted.heap assignmentTyped snapshot write).1,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩, agreement⟩

include transport environments heaps locals agrees initial admitted in
theorem preserves_fault (errors : head.Errors faults) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
      environment before assignment.target reason before) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents values.checked registry functions finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
    head.preserves_fault functions program invocation.evidence environments heaps locals agrees errors trace next output
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    callerProtocol transport initial maps worlds frame metadata
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
    reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
/-! Ordered initialization and the finite loop reconstruct the original Source
statement, including the suffix reached in the restored outer environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts
variable {program : Program} {stages : Registry} {invocation : Scope}
  {context finalContext : SourceSemantics.Context} {environment inner : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {initial post : List ForItemForm}
  {test : ExpressionId} {body rest : List StatementId} {size tailSize : Nat}
  {id : StatementId} {node : StatementNode} {mode : Bool} {outcome : BodyOutcome}

theorem closed
    (trace : Trace program stages invocation context environment before initial test post body size outcome after) :
    outcome.NoEscapedControl := by
  cases trace with
  | initializerFault _ => exact .fault _
  | @loop _ _ _ _ _ result _ initialized executed =>
    have closed := SelectedCompilationStageLoopOutcomes.for_closed executed
    cases result with
    | returned => exact .returned _
    | fault => exact .fault _
    | fallthrough => exact .fallthrough _
    | breaking => exact (closed.1 _ rfl).elim
    | continuing => exact (closed.2 _ rfl).elim

theorem fallthrough_environment
    (trace : Trace program stages invocation context environment before initial test post body size (.fallthrough inner) after) :
    inner = environment := by
  generalize resultEq : BodyOutcome.fallthrough inner = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop _ _ _ _ _ result _ _ _ => cases result <;> simp_all [BodyOutcome.restore]

theorem loop_restore
    (trace : Size.ForLoop program stages size invocation context environment before test post body outcome after) :
    outcome.restore environment = outcome := by
  cases outcome with
  | fallthrough inner =>
      cases CallableIndexedOwnedPreparedStagedScopedForSourceInversion.fallthrough_environment trace
      rfl
  | returned | fault => rfl
  | breaking => exact ((SelectedCompilationStageLoopOutcomes.for_closed trace).1 _ rfl).elim
  | continuing => exact ((SelectedCompilationStageLoopOutcomes.for_closed trace).2 _ rfl).elim

theorem returned {value : Dynamic.Value}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.returned value) after) :
    Size.StatementsIn program stages mode size invocation context environment before (id :: rest) context (.returned value) after := by
  generalize resultEq : BodyOutcome.returned value = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      exact .forReturned (lookupStatement?_sound found) form initializedTrace loopTrace

theorem fault {failure : Failure}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.fault failure) after) :
    Size.StatementsIn program stages mode size invocation context environment before (id :: rest) context (.fault failure) after := by
  generalize resultEq : BodyOutcome.fault failure = result at trace
  cases trace with
  | initializerFault initializedTrace =>
      cases resultEq
      exact .forInitializerFault (lookupStatement?_sound found) form initializedTrace
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      exact .forFault (lookupStatement?_sound found) form initializedTrace loopTrace

theorem fallthrough
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.fallthrough environment) middle)
    (tail : Size.StatementsIn program stages mode tailSize invocation context environment middle rest finalContext outcome after) :
    Size.StatementsIn program stages mode (size + tailSize) invocation context environment before (id :: rest) finalContext outcome after := by
  generalize resultEq : BodyOutcome.fallthrough environment = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      have same := CallableIndexedOwnedPreparedStagedScopedForSourceInversion.fallthrough_environment loopTrace
      subst same
      simpa only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm tailSize 1] using
        (Size.StatementsIn.forFallthrough (mode := mode) (rest := rest)
          (lookupStatement?_sound found) form initializedTrace loopTrace tail)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSequences
/-! Finite staged loops compose with the actual following statements.
Loop completion restores the original lexical context and environment while
retaining every iteration's heap effects and captured cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {test : ExpressionId} {items post : List ForItemForm} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {headCode : Expr}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

include bridge functions condition in
theorem reflects {budget : Nat}
    (correct : CallableIndexedOwnedAdmittedStagedForHeadContracts.Reflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type headCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test post statements)
    (remaining : FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, headRelated, headPost⟩ :=
    correct (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted headEval
  cases represented with
  | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).1 innerEnvironment rfl).elim
  | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).2 innerEnvironment rfl).elim
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have same := CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough_environment headTrace
      subst innerEnvironment
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, reached, tailRelated, post⟩ :=
        remaining (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) reference
          ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditioned headPost
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, reached,
        callerProtocol.trans headRelated tailRelated, post⟩

include bridge functions condition in
theorem preserves {budget : Nat}
    (correct : CallableIndexedOwnedAdmittedStagedForHeadContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type headCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test post statements)
    (remaining : FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace program stages invocation context environment before items test post statements headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, reached, related, post⟩ :=
      correct bounded environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted headTrace
    cases represented with
    | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).1 innerEnvironment rfl).elim
    | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).2 innerEnvironment rfl).elim
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedForSourceInversion.initial_loop_and_tail unique statementFound form trace with
    ⟨initialSize, failedContext, failure, sameSize, _contextEq, outcomeEq, initialTrace⟩ |
    ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, sourceValue, sameSize, _contextEq, outcomeEq, initialTrace, loopTrace⟩ |
    ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, failure, sameSize, _contextEq, outcomeEq, initialTrace, loopTrace⟩ |
    ⟨initialSize, loopSize, tailSize, loopContext, loopEnvironment, initialized, middle, sameSize, initialTrace, loopTrace, tailTrace⟩
  · subst outcome
    exact finish (.initializerFault initialTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.loop initialTrace loopTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.loop initialTrace loopTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · have headWithin : Staging.Recursive.Size.stepSize [initialSize, loopSize] ≤ budget := Nat.le_trans (by
      rw [sameSize]
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, middleState, headRelated, headPost⟩ :=
      correct headWithin environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted (.loop initialTrace loopTrace)
    cases represented with
    | fallthrough _ _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, reached, tailRelated, post⟩ :=
          remaining tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned headPost tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, reached, callerProtocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForEdges
/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (FlowPreserves FlowReflects)
open TypedLexicalWhile (Progress)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body postCode : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

theorem condition_preserves_at {size : Nat}
    (meaning : PreservesAt bridge context model stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    meaning tree found typed state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ReflectsAt bridge context model stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    reflection tree found typed state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : FlowPreserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : FlowReflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
/-! The compiler's post header returns to the loop's lexical context. Its
original item trace retains every intermediate binding and reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

def restoredOutcome (environment : Dynamic.Environment) :
    Staging.Recursive.ForItemsOutcome → Staging.Recursive.BodyOutcome
  | .done _ => .fallthrough environment
  | .fault failure => .fault failure

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- The actual post header restores its outer lexical context after completion.
Its Source trace retains the real final header context and all heap effects. -/
def Reflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (items : List ForItemForm) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before
        items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

/-- Source post execution retains the reached heap and restores admission at
the loop context before the next condition. -/
def Preserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (items : List ForItemForm) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome} {after : Dynamic.Heap},
      Staging.Recursive.Size.ForItems program stages size invocation context environment before
        items finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForPostContracts
open TypedLexicalWhile (Progress)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body postCode : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem preserves_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : Preserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (TypedImperativeFor.postValues type location continuing ++ actual) store
        (ForLoop.postCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, postTyped⟩ := TypedImperativeFor.postValues_typed continuing state.live.selfTyped state.live.actualTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals postAgrees postTyped
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [TypedImperativeFor.post_rename] using evaluated,
    represented, progress, reached, retained, post⟩

theorem reflects_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : Reflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (TypedImperativeFor.postValues type location continuing ++ actual) store
      (ForLoop.postCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, postTyped⟩ := TypedImperativeFor.postValues_typed continuing state.live.selfTyped state.live.actualTyped
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals postAgrees postTyped
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [TypedImperativeFor.post_rename] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForIterations
/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForIterations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (FlowPreserves FlowReflects)
open TypedLexicalWhile (Progress)
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedAdmittedStagedForEdges
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {condition : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : FlowReflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Reflects (administrative := administrative)
      (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation)) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) →
      guard contextLocation native → Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before condition post statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state native fixedRead guarded ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld,
        conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at bridge functions (children _ (Nat.lt_of_lt_of_le conditionSmaller bounded))
        tree found typed agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .testFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases boolean with
      | false =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .finished conditionTrace, .fallthrough environment (.inl rfl),
          conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
      | true =>
        obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
        obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
        obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace,
            bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost⟩ :=
          body_reflects_at bridge functions guard correct
            (Nat.le_trans (Nat.le_of_lt bodySmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
            agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
            guarded conditionPost.at_value.2 bodyEval
        have progress := conditionProgress.trans bodyProgress
        cases bodyRelated with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .bodyFailure conditionTrace bodyTrace, .fault matched,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | returned payload =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .returnedFromBody conditionTrace bodyTrace, .returned payload,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | fallthrough innerEnvironment allowed =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CallableIndexedOwnedAdmittedStagedForPostEdges.reflects_at (continuing := false) bridge functions guard postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees reference bodyState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
              guarded bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .postFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_fallthrough branch bodyEval.sound postEval.sound postState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .iterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

        | breaking innerEnvironment =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .forBreakFromBody conditionTrace bodyTrace,
            .fallthrough environment (.inl rfl), progress, bodyState,
            callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | continuing innerEnvironment =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CallableIndexedOwnedAdmittedStagedForPostEdges.reflects_at (continuing := true) bridge functions guard postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees reference bodyState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
              guarded bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .continuePostFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_continuing branch bodyEval.sound postEval.sound postState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .continueIterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : FlowPreserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves (administrative := administrative)
      (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation)) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) →
      guard contextLocation native → Admission bridge context state.retained →
      Staging.Recursive.Size.ForLoop program stages size invocation context environment before condition post statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state native fixedRead guarded ready trace
    cases trace with
    | finished testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_false conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | testFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_failure conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returnedFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | forBreakFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | breaking innerEnvironment =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFailure testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fault matched =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := false) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_fallthrough_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | iterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := false) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_fallthrough conditionEval bodyEval postEval postState.live.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

    | continuePostFailure testTrace bodyTrace postTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := true) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_continuing_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | continueIterate testTrace bodyTrace postTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge functions
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge functions guard correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2
              guarded conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CallableIndexedOwnedAdmittedStagedForPostEdges.preserves_at (continuing := true) bridge functions guard postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees reference bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2
                guarded bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2
                  guarded postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_continuing conditionEval bodyEval postEval postState.live.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForIterations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads
/-! The authentic loop prelude installs a self cell without changing the Source
heap. Finite staged iterations retain its exact reached caller and state; a
fallthrough result returns to the original lexical context and environment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchReflects BranchPreserves)
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {post : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {selfReason : Word}

include bridge functions condition transport in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Reflects (administrative := administrative)
      (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope post expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before test post statements outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    ProtectedStateTransition.For.initial_state (protocol := callerProtocol)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (functions := functions) transport environments heaps locals agrees
      actualTyped read unmapped nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.2.2.2.1 installedRelated installedRecords admitted
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  rw [LoopRenaming.iterate] at completed
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := completed.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedForIterations.reflects bridge functions condition
      children found nodeType typed generated correct postCorrect agrees reference entrySize
      (Nat.le_trans (Nat.le_of_lt entrySmaller) within) protectedState installedRead conditioned activated nativeEntry
  have total := installedProgress.trans progress
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    total.1, total.2.1, total.2.2.1, total.2.2.2.1, total.2.2.2.2,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

include bridge functions condition transport in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    (postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves (administrative := administrative)
      (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope post expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.ForLoop program stages size invocation context environment before test post statements outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    ProtectedStateTransition.For.initial_state (protocol := callerProtocol)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (functions := functions) transport environments heaps locals agrees
      actualTyped read unmapped nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.2.2.2.1 installedRelated installedRecords admitted
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedForIterations.preserves bridge functions condition
      children found nodeType typed generated correct postCorrect agrees reference size within protectedState
      installedRead conditioned activated trace
  have total := installedProgress.trans progress
  exact ⟨value, finalStore, finalMap, finalWorld,
    by
      rw [LoopRenaming.iterate]
      apply LocalLoop.iterate_evaluates
      apply LocalLoop.invoke_success _ _ (.var rfl) _ nativeTrace
      exact protectedState.live.selfRead,
    represented, total.1, total.2.1, total.2.2.1, total.2.2.2.1, total.2.2.2.2,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
/-! Actual completed post-header code determines its staged item trace and
restores the outer caller while retaining all allocations and capture writes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (ItemShape)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open GenericForHeader (Tree)
open TypedLexicalControl (sequence_rename)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

theorem fault_post {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    {expected : TypeSystem.Ty} {failure : Staging.Recursive.Failure}
    (reached : callerProtocol.State index)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached)) :
    PostAdmission bridge context expected (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨stable, by intro value same; cases same⟩
  | stage origin call reason => exact stable

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (diagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions callerProtocol invocation.source
    invalidProjection missingDefault receiving (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents model mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents model mapping world false expected type faults (restoredOutcome second outcome) value := by
  cases outcome with
  | done environment => cases related with | fallthrough _ allowed => exact .fallthrough _ allowed
  | fault failure => exact related

private theorem post_environment {context expected outcome first second index}
    {reached : callerProtocol.State index}
    (post : Post bridge context expected (restoredOutcome first outcome) reached) :
    Post bridge context expected (restoredOutcome second outcome) reached := by
  cases outcome <;> exact post

include bridge bindings definitions registered producer acquire transport extension functionTypes faithful observations diagnostics in
/-- Native completion determines the actual ordered lexical Source trace,
including the distinct context after successful allocation and initializer
faults before allocation. The returned caller state retains the entire heap. -/
theorem reflects_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before
        items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached := by
  induction catalogSites generalizing size mapping world actualContext environment canonical actual before
      store finalStore ξ contextLocation native value with
  | @nil context scope code next =>
      change code = LocalLoop.fallthrough type at next
      subst code
      rw [LoopRenaming.fallthrough] at completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.fallthrough_evaluates type actual store)
      exact ⟨_, context, .done environment, before, mapping, world, .empty,
        .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended) (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .absent mono extended .append trace,
        (rep_environment functions represented), finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initialFound sourceType child allocation annotation same remaining tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename] at completed
      obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := completed.bind_computation
      obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented,
          middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
        children context initialSize (Nat.lt_of_lt_of_le initialSmaller within) certified initialFound typed
          environments heaps locals agrees actualTyped initial admitted initialEval
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact ⟨Staging.Recursive.Size.stepSize [initialSourceSize], context, _, middle, middleMap, middleWorld,
            .initializerFault mono initialTrace, .fault matched,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
              nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended) (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .initialized mono extended initialTrace .append trace,
            (rep_environment functions related), finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @discard context scope expression expressionNode rest lowered body expressionFound child remaining tailSites ih =>
      have tailShape := shape.discard_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard] at completed
      obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
          middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
        children context childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted childEvaluation
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
            .expressionFailure childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped) (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .expression childTrace tailTrace, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope assignment operator rhs rest body head remaining tailSites headErrors ih =>
      have invalidToken : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid := PreparedAssignmentReachedDiagnostics.operands headErrors semantic
      obtain ⟨_profile, tailShape⟩ := shape.assignment_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      · have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
          head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          budget typedChildren invalidToken completed within
        cases result with
        | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignmentFailure snapshot trace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignmentOperands snapshot trace currentRead rootType initialized path invalid, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected)
              (failure := .semantic (.invalidAssignmentOperands operator)) reached stable
        | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2
            obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
              .assignment snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
      · have errors := PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic diagnostics assignmentTyped initial
        have result := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.reflects_bounded
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations head bare
          environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          budget typedChildren functionTypes errors completed within
        cases result with
        | keyFault ready keysTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentKeysFault bare ready keysTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | getterFault keysTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentGetterFault bare keysTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | rhsFault keysTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentRhsFault bare keysTrace snapshot childTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | writeFault keysTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentWriteFault bare keysTrace snapshot childTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | success keysTrace snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
            .projectedAssignment bare keysTrace snapshot childTrace write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @bitNot context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_profile, bare, tailShape⟩ := shape.bitNot_tail head.bare
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      have result := CallableIndexedOwnedAdmittedStagedBareBitNotHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions transport
        head environments heaps locals agrees actualTyped initial admitted assignmentTyped headErrors completed
      cases result with
      | fault trace same matched finalHeaps maps worlds preservation reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [], context, _, _, _, _,
            .bitNotFault head.bare trace, .fault (semantic _ _ matched),
            finalHeaps, maps, worlds, preservation, .refl _, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .bitNot snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩

  | @bitNotProjected context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_profile, tailShape⟩ := shape.unary_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with | intro typed _ => exact typed
      have errors := PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment)
        headErrors diagnostics targetTyped initial
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.reflects_bounded
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        bridge functions extension transport faithful observations head head.projected
        environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
        budget typedChildren functionTypes errors completed within
      cases result with
      | keyFault ready keysTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
        cases same
        exact ⟨_, context, _, _, _, _, .projectedBitNotKeysFault head.projected ready keysTrace, .fault matched,
          finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
      | getterFault keysTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
        cases same
        exact ⟨_, context, _, _, _, _, .projectedBitNotGetterFault head.projected keysTrace failed, .fault matched,
          finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
      | success keysTrace snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
        have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2
        obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted
            (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .projectedBitNot head.projected keysTrace snapshot write trace, represented,
          finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
          metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
/-! Actual staged post-header execution determines the emitted native result.
The outer caller is restored while allocations and capture writes are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (ItemShape)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open GenericForHeader (Tree)
open TypedLexicalControl (sequence_rename)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

theorem fault_post {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    {expected : TypeSystem.Ty} {failure : Staging.Recursive.Failure}
    (reached : callerProtocol.State index)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached)) :
    PostAdmission bridge context expected (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨stable, by intro value same; cases same⟩
  | stage origin call reason => exact stable

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (diagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions callerProtocol invocation.source
    invalidProjection missingDefault receiving (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents model mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents model mapping world false expected type faults (restoredOutcome second outcome) value := by
  cases outcome with
  | done environment => cases related with | fallthrough _ allowed => exact .fallthrough _ allowed
  | fault failure => exact related

private theorem post_environment {context expected outcome first second index}
    {reached : callerProtocol.State index}
    (post : Post bridge context expected (restoredOutcome first outcome) reached) :
    Post bridge context expected (restoredOutcome second outcome) reached := by
  cases outcome <;> exact post

include bridge bindings definitions registered producer acquire transport extension faithful observations diagnostics in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before
      items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached := by
  induction catalogSites generalizing size mapping world actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @nil context scope code next =>
      obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.empty trace
      change code = LocalLoop.fallthrough type at next
      subst code
      rw [LoopRenaming.fallthrough]
      exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates type actual store,
        .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended) tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, (rep_environment functions represented), finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initialFound sourceType child allocation annotation same remaining tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized mono extended trace with
        ⟨initialSize, failure, sameSize, contextEq, outcomeEq, initialTrace⟩ |
        ⟨initialSize, tailSize, sourceValue, location, middle, bound, sameSize, initialTrace, allocated, remainingTrace⟩
      · subst finalContext
        subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
            obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
                nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
              CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
                mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
                reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) initialPost.at_value.2
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
              ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended) tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), (rep_environment functions related), finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @discard context scope expression expressionNode rest lowered body expressionFound child remaining tailSites ih =>
      have tailShape := shape.discard_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
            middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
                finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
              ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped) tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope assignment operator rhs rest body head remaining tailSites headErrors ih =>
      have invalidToken : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid := PreparedAssignmentReachedDiagnostics.operands headErrors semantic
      obtain ⟨_profile, tailShape⟩ := shape.assignment_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      · obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
          (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          functions extension head bare environments heaps locals agrees
        rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot trace with
          ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
          ⟨childSize, right, currentCell, initialValue, selected, sameSize, contextEq, outcomeEq,
            childTrace, _currentRead, _rootType, _initialized, _path, invalidOperands⟩ |
          ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
        · subst finalContext
          subst outcome
          have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) childTrace body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge reached stable⟩
        · subst finalContext
          subst outcome
          have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_operands
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) snapshot invalidOperands childTrace body (LocalLoop.controlType type) invalidToken
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected)
              (failure := .semantic (.invalidAssignmentOperands operator)) reached stable⟩
        · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
          have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
              count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) snapshot childTrace write
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2 tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted remainingTrace
          have native := (continuation body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
              SourceCoreDataPlaces.shift] using evaluated)
          exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
            maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
            last, callerProtocol.trans related lastRelated, post⟩
      · have errors := PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic diagnostics assignmentTyped initial
        cases trace with
        | assignment snapshot _ _ _ => cases snapshot with | intro empty _ _ _ => exact (bare empty).elim
        | assignmentFailure snapshot _ => cases snapshot with | intro empty _ _ _ => exact (bare empty).elim
        | assignmentOperands snapshot _ _ _ _ _ _ => cases snapshot with | intro empty _ _ _ => exact (bare empty).elim
        | unbound empty _ => exact (bare empty).elim
        | dangling empty _ _ => exact (bare empty).elim
        | projectedAssignmentRootFault _ failed => exact (failed.excluded head.writable locals).elim
        | projectedAssignmentKeysFault _ ready keysTrace =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_key_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren ready keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | projectedAssignmentGetterFault _ keysTrace failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_getter_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren errors keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              failed body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | projectedAssignmentRhsFault _ keysTrace snapshot childTrace =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | projectedAssignmentWriteFault _ keysTrace snapshot childTrace failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_write_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren errors keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              failed body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | projectedAssignment _ keysTrace snapshot childTrace write remainingTrace =>
          obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
              count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega) write
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2
              (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted remainingTrace
          have native := (continuation body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
              SourceCoreDataPlaces.shift] using evaluated)
          exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
            maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
            last, callerProtocol.trans related lastRelated, post⟩
  | @bitNot context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_word, _bare, tailShape⟩ := shape.bitNot_tail head.bare
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot head.bare trace with
        ⟨reason, sameSize, contextEq, outcomeEq, heapEq, failed⟩ |
        ⟨tailSize, target, updated, written, sameSize, snapshot, write, remainingTrace⟩
      ·
        subst finalContext
        subst outcome
        subst after
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions transport head environments heaps locals agrees initial admitted
            headErrors failed body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault (semantic _ _ matched), finalHeaps,
          maps, worlds, preservation, .refl _, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic reason) reached stable⟩
      · have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
            count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_value
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions transport head environments heaps locals agrees actualTyped initial admitted assignmentTyped
            snapshot write
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2 tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted remainingTrace
        have native := (continuation body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using evaluated)
        exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
          maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
          last, callerProtocol.trans related lastRelated, post⟩

  | @bitNotProjected context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_word, tailShape⟩ := shape.unary_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with | intro typed _ => exact typed
      have errors := PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment)
        headErrors diagnostics targetTyped initial
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      cases trace with
      | bitNot snapshot _ _ =>
        have empty : assignment.target.projections = [] := by cases snapshot; assumption
        exact (head.projected empty).elim
      | bitNotFault empty _ => exact (head.projected empty).elim
      | projectedBitNotRootFault _ failed => exact (failed.excluded head.writable locals).elim
      | projectedBitNotKeysFault _ ready keysTrace =>
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_key_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            budget typedChildren ready keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
            body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
          preservation, metadata, reached, related, fault_post bridge reached stable⟩
      | projectedBitNotGetterFault _ keysTrace failed =>
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_getter_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension transport faithful observations head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            budget typedChildren errors keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
            failed body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
          preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
      | projectedBitNot _ keysTrace snapshot write remainingTrace =>
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
            count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_value
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension transport faithful observations head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            budget typedChildren keysTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
            snapshot write
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2
            (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within; omega)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted remainingTrace
        have native := (continuation body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using evaluated)
        exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
          maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
          last, callerProtocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
/-! Projected unary inversion retains the actual key endpoint and written suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

inductive Result (program : Program) (registry : Registry) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (rest : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (body : List StatementId) :
    Nat → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after
  | success {keysSize tailSize values target targetHeap updated written outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        targetHeap target updated written)
      (next : Trace program registry invocation context environment written rest test post body tailSize outcome after) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [keysSize, tailSize]) outcome after

private theorem fault_grade (keys tail : Nat) :
    Size.stepSize [Size.stepSize [keys, tail]] = Size.stepSize [keys, Size.stepSize [tail]] := by
  simp [Size.stepSize]
  omega

private theorem loop_grade (keys tail loop : Nat) :
    Size.stepSize [Size.stepSize [keys, tail], loop] = Size.stepSize [keys, Size.stepSize [tail, loop]] := by
  simp [Size.stepSize]
  omega

theorem projected_bitNot {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {assignment : AssignmentResolution} {test : ExpressionId}
    {items post : List ForItemForm} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (projected : assignment.target.projections ≠ [])
    (trace : Trace program registry invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    Result program registry invocation context environment before assignment items test post body size outcome after := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | bitNot snapshot _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | bitNotFault empty _ => exact (projected empty).elim
    | projectedBitNotRootFault _ failed => exact .rootFault failed
    | projectedBitNotKeysFault _ ready keys => exact .keysFault ready keys
    | projectedBitNotGetterFault _ keys failed => exact .getterFault keys failed
    | projectedBitNot _ keys snapshot write next =>
      have result := Result.success (test := test) (post := post) (body := body) keys snapshot write (Trace.initializerFault next)
      simpa only [fault_grade] using result
  | loop initial loop =>
    cases initial with
    | bitNot snapshot _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | projectedBitNot _ keys snapshot write next =>
      have result := Result.success keys snapshot write (Trace.loop next loop)
      simpa only [loop_grade] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
/-! Projected assignment inversion retains each evaluated key, the getter
snapshot, the reached RHS heap and the actual statement suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

inductive Result (program : Program) (registry : Registry) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (rest : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (body : List StatementId) :
    Nat → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after
  | rhsFault {keysSize childSize values target targetHeap failure after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.fault failure) after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault failure) after
  | writeFault {keysSize childSize values target targetHeap right reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) after)
      (failed : ProjectedTarget.WriteFault operator target right after reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault (.semantic reason)) after
  | success {keysSize childSize tailSize values target targetHeap right middle updated written outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated written)
      (next : Trace program registry invocation context environment written rest test post body tailSize outcome after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [keysSize, childSize, tailSize]) outcome after

private theorem fault_grade (keys child tail : Nat) :
    Size.stepSize [Size.stepSize [keys, child, tail]] = Size.stepSize [keys, child, Size.stepSize [tail]] := by
  simp [Size.stepSize]
  omega

private theorem loop_grade (keys child tail loop : Nat) :
    Size.stepSize [Size.stepSize [keys, child, tail], loop] = Size.stepSize [keys, child, Size.stepSize [tail, loop]] := by
  simp [Size.stepSize]
  omega

theorem projected_assignment {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs test : ExpressionId}
    {items post : List ForItemForm} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (projected : assignment.target.projections ≠ [])
    (trace : Trace program registry invocation context environment before
      (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    Result program registry invocation context environment before assignment operator rhs items test post body size outcome after := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | assignment snapshot _ _ _ | assignmentFailure snapshot _ | assignmentOperands snapshot _ _ _ _ _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | unbound empty _ | dangling empty _ _ => exact (projected empty).elim
    | projectedAssignmentRootFault _ failed => exact .rootFault failed
    | projectedAssignmentKeysFault _ ready keys => exact .keysFault ready keys
    | projectedAssignmentGetterFault _ keys failed => exact .getterFault keys failed
    | projectedAssignmentRhsFault _ keys snapshot child => exact .rhsFault keys snapshot child
    | projectedAssignmentWriteFault _ keys snapshot child failed => exact .writeFault keys snapshot child failed
    | projectedAssignment _ keys snapshot child write next =>
      have result := Result.success (test := test) (post := post) (body := body) keys snapshot child write (Trace.initializerFault next)
      simpa only [fault_grade] using result
  | loop initial loop =>
    cases initial with
    | assignment snapshot _ _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | projectedAssignment _ keys snapshot child write next =>
      have result := Result.success keys snapshot child write (Trace.loop next loop)
      simpa only [loop_grade] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem bitNot {assignment : AssignmentResolution}
    (bare : assignment.target.projections = [])
    (trace : Trace program stages invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    (∃ reason, size = Size.stepSize [Size.stepSize []] ∧ outcome = .fault (.semantic reason) ∧
      after = before ∧ Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
        environment before assignment.target reason before) ∨
    (∃ tailSize target updated written, size = Size.stepSize [tailSize] ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      Trace program stages invocation context environment written items test post body tailSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot bare initial with failed | continued
      · obtain ⟨reason, rfl, _, same, sameHeap, failed⟩ := failed
        cases same
        exact .inl ⟨reason, rfl, rfl, sameHeap, failed⟩
      · obtain ⟨tailSize, target, updated, written, rfl, snapshot, write, next⟩ := continued
        exact .inr ⟨_, target, updated, written, rfl, snapshot, write, .initializerFault next⟩
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot bare initial with failed | continued
      · obtain ⟨_, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨tailSize, target, updated, written, rfl, snapshot, write, next⟩ := continued
        refine .inr ⟨_, target, updated, written, ?_, snapshot, write, .loop next loop⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
end
