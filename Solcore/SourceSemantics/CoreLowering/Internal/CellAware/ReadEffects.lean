import Solcore.SourceSemantics.CoreLowering.CompatibleCellBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.Staging.RecursiveBareBitNot
import Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductSource
import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadCompletion
import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SelectedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedExpressions
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies

/-!
# Cell-aware reads and builtin values

Effects and meaning of reads, read products and their completion, builtin value certificates and origins, native body trees, and the prefixes of matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareBareBitNotHeads
/-! Bare unary heads retain the actual caller state and exact written heap.
The operation has no expression child; its native continuation still supplies
its genuine strict evaluation bound. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBareBitNotHeads
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
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
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
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld before finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld before finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions cells instances context invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | success {remainingSize : Nat} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
      {after : Dynamic.Heap} {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions cells instances context invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore

variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} (head : CompatibleBitNotStatements.Head context scope assignment)
  {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel values.checked registry functions) cells)
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)

include transport ordinaryCells environments heaps locals agrees actualTyped initial admitted assignmentTyped in
theorem reflects_bounded (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) :
    ResultAt bridge size values.checked registry functions cells instances context invocation faults scope
      (head.writtenContext actualContext) assignment environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore := by
  rcases head.reflects_cells_sized (source := invocation.source) functions program invocation.evidence environments ordinaryCells heaps locals agrees actualTyped admitted.heap errors completed with failed | succeeded
  · obtain ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, same, matched, finalHeaps,
      maps, worlds, frame, metadata, effect⟩ := failed
    have trace := trace.sound
    cases Staging.Recursive.bitNot_fault_heap head.bare trace
    obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
      callerProtocol transport initial maps worlds frame metadata
    exact .fault trace same matched finalHeaps maps worlds frame effect reached related
      (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
  · obtain ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize,
      trace, finalHeaps, maps, worlds, frame, metadata, effect, count, typed, bounded, remaining⟩ := succeeded
    cases trace.sound with
    | intro resolved write =>
      obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves head.bare resolved
      obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
        callerProtocol transport initial maps worlds frame metadata
      exact .success snapshot write finalHeaps maps worlds frame metadata effect count typed reached related
        ⟨(Staging.Recursive.SelectedPreservation.bare_write_bitNot locals admitted.heap assignmentTyped snapshot write).1,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩ bounded remaining

include transport ordinaryCells environments heaps locals agrees actualTyped initial admitted assignmentTyped in
theorem preserves_value {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value} {after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      before target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect, count, typed, agreement⟩ :=
    head.preserves_prefix_cells functions program invocation.evidence environments ordinaryCells heaps locals agrees actualTyped
      (.intro (snapshot.resolves program context invocation.evidence invocation.source) write)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    callerProtocol transport initial maps worlds frame metadata
  exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect, count, typed,
    ⟨reached, related,
      (Staging.Recursive.SelectedPreservation.bare_write_bitNot locals admitted.heap assignmentTyped snapshot write).1,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩, agreement⟩

include transport ordinaryCells environments heaps locals agrees initial admitted in
theorem preserves_fault (errors : head.Errors faults) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
      environment before assignment.target reason before) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.CellHeapRepresents cells finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld before finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect⟩ :=
    head.preserves_fault_cells functions program invocation.evidence environments ordinaryCells heaps locals agrees errors trace next output
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    callerProtocol transport initial maps worlds frame metadata
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, effect,
    reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareBareBitNotHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
/-! Positive callable leaves for heaps containing generalized descriptors.
A materialized local keeps its actual read wrapper and Source instantiation;
there is no projection of that branch to an older lexical closure history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | ordinary {sourceType source native type}
      (retained : CallableIndexedOwnedPreparedPhysicalCellOrigins.FunctionOrigins
        headers keys bodyRegistry faults mapping world sourceType source native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType source native type
  | generalized {function native bindings parameter result}
      (member : GeneralizedLocalMaterializedAssociation.Association compiled
        mapping world function native bindings parameter result)
      (owner : OwnedKey keys) (framed : member.AtFrame owner.key.frameLocation) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)

def functions (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).projection
        (registry := registry) retained
    | generalized member _ _ => exact member.projection
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).runtime_hasType
        (registry := registry) retained
    | generalized member _ _ => exact member.runtime_hasType
  source_function := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).source_function
        (registry := registry) retained
    | generalized => exact .closure _
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      related registries maps worlds
    cases related with
    | ordinary retained =>
      exact .ordinary ((CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).extend
        retained registries maps worlds)
    | generalized member owner framed =>
      exact .generalized (member.extend maps worlds) owner (by cases member; exact framed)

theorem includes_prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).Includes
      (functions headers keys bodyRegistry faults profile) := fun represented => .ordinary represented

theorem runtime_views (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  cases related with
  | ordinary retained => exact CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile (registry := registry) retained
  | generalized => exact (Dynamic.ValueRuntimeType.closure _).matches

theorem observations (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | ordinary retained => exact CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile retained
  | generalized member _ _ =>
    cases member with
    | viewed material view typed => exact .contractedAnonymous _ _ _ _ _ profile

theorem builtin (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile) mapping world sourceType source native type) :
    ∀ function, source = .builtin function →
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world sourceType (.builtin function) native type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | ordinary retained =>
      exact SelectedCompilationBuiltinFunctionOrigins.prepared_builtin profile (.function retained)
    | generalized => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function selected
    exact .compatible same (ih function selected)
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

theorem stage_origin (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile) mapping world sourceType source native type) :
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro shape
    cases related with
    | ordinary retained => exact SelectedCompilationCallableOrigins.prepared_origin profile (registry := registry) (.function retained) shape
    | generalized member _ _ => exact member.stage_origin
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance origins (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry faults profile
      (functions headers keys bodyRegistry faults profile) where
  toErasesBuiltinsToContextual := ⟨fun represented => builtin profile represented _ rfl⟩
  origin := stage_origin profile

end Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinPackedApplication
/-! The authentic builtin identity supplies its ordered parameter row in a mixed heap. The
primitive application proof keeps the caller, heap and store unchanged while
relating the actual result to independent Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinPackedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CellAwarePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {bodyFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (cells : GenericHeap.CellModel compiled.indexed.layouts.definitions)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : BuiltinFunctionId} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.builtin ⟨function⟩) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile)
    mapping world (.function parameter result) (.builtin ⟨function⟩) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Actual complete builtin execution determines the same Source primitive
result and unchanged caller; no builtin body law is supplied by a caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
    (CellAwarePhysicalFunctionOrigins.builtin profile calleeRelated ⟨function⟩ rfl) ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceResult, trace, representedResult, applied, finalStoreEq⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects functions (CellAwarePhysicalFunctionOrigins.observations profile) builtin rows evaluation
  subst finalStore
  rw [← signature.2, ← nativeTypes.2] at representedResult
  refine ⟨sources, packing, rows.length.1.symm ▸ RecursivePublicCallableArity.Arity.builtin ⟨function⟩, Staging.Recursive.Size.stepSize [], .value sourceResult,
    before, mapping, world, trace, representedResult, heaps, .refl _, .refl _, .refl _ _, .refl _,
    caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed
  exact ⟨sources, packing, meaning⟩

include profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- The actual primitive argument arity fixes its unpacking. Typed primitive
inputs exclude Source dispatch faults; all caller state remains unchanged. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
    (CellAwarePhysicalFunctionOrigins.builtin profile calleeRelated ⟨function⟩ rfl) ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have arity : function.parameterTypes.length = sources.length := arityAt.builtin_count
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (rows.length.1.symm.trans arity)
  subst decodedSources
  obtain ⟨nativeSize, value, evaluated, representedResult, sameHeap, _sourceGrade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions (CellAwarePhysicalFunctionOrigins.observations profile) builtin rows trace
  subst after
  rw [← signature.2, ← nativeTypes.2] at representedResult
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value store := by
    rw [packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail evaluated
  obtain ⟨source, sameOutcome, _sameHeap, _size, applied⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions (CellAwarePhysicalFunctionOrigins.observations profile) rows trace
  cases sameOutcome
  refine ⟨value, store, mapping, world, padded.sound, representedResult, heaps,
    .refl _, .refl _, .refl _ _, .refl _, caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed profile cells caller stable heapTyped calleeTyped calleeRelated heaps packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinPackedApplication
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
/-! A builtin value retains the actual accepted reference, source occurrence,
nonwrapping identity and descriptor from the compiled artifact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
open Core Frontend SourceInference
open CallableIndexedBuiltinValues (Prepared)

structure Header {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (source : TypedSource) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  name : String
  function : BuiltinFunctionId
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.builtinFunction function)
  requirements : node.requirements = []
  coercions : node.coercions = []
  sourceType : node.type = function.type
  index : Nat
  identity : Word
  inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index)
  number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity
  descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function)
  nativeType : lowered.type = CallableContract.functionType
    (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
  emitted : lowered.expression = BuiltinCalls.Protocol.contracted function identity descriptor.id

theorem of_reference {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {name : String}
    {function : BuiltinFunctionId} {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : SourceCoreFunctions.Context}
    (globals : compilation.globals = prepared.base.globals)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
      compilation source node name function = .ok lowered) : Nonempty (Header prepared source id lowered) := by
  rw [prepared.ancestry.graph.inputs.callableSelected] at accepted
  have reference := BuiltinCalls.reference_of_accepted accepted
  cases reference with
  | @intro index identity expression spelling sourceType inventory number decorated =>
    cases descriptorFound : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function) with
    | error error =>
      simp [SourceCoreGeneralFunctions.callablePolicy, descriptorFound, bind, Except.bind, Except.mapError] at decorated
    | ok descriptor =>
      have emitted := ActualCallablePolicy.builtin_decoration prepared.ancestry.graph.inputs.callable [] compilation source node
        function (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)) descriptor
      have same := Except.ok.inj (emitted.symm.trans decorated)
      subst expression
      exact ⟨⟨node, name, function, found, form, requirements, coercions, sourceType,
        index, identity, inventory, by simpa only [globals] using number, descriptor, rfl, rfl⟩⟩

/-- Renaming a builtin reference keeps its closed builtin body and captures
exactly the current actual environment at evaluation. -/
theorem Header.rename {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : TypedSource} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Header prepared source id lowered) (embedding : Nat → Nat) :
    lowered.expression.rename embedding = lowered.expression := by
  rw [receipt.emitted]
  have closed : ∀ (function : BuiltinFunctionId) (identity contract : Word),
      (BuiltinCalls.Protocol.contracted function identity contract).rename embedding =
        BuiltinCalls.Protocol.contracted function identity contract := by
    intro function identity contract
    cases function <;> rfl
  exact closed receipt.function receipt.identity receipt.descriptor.id

end Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
/-! Genuine builtin receipts enter the mixed positive function model without
changing their descriptor, native closure, or captured runtime environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem included (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | builtin selected number descriptor typed =>
    exact .ordinary (.builtin (.prior (.prior (.builtin (.builtin selected number descriptor typed)))))

end Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
/-! A real local read retains its original descriptor and requirement outcome.
With no output coercion, the staged read has exactly the same value or fault
and reached heap; no native execution or cell classification is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
open Frontend SourceInference Staging.Recursive Staging.Recursive.Lifting

theorem read {program : Program} {registry : Registry} {invocation : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (empty : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Expression program registry invocation context environment before id (embed outcome) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      cases same_node contains
      rw [empty] at path
      cases path
      rw [empty] at raw
      exact .atomicValue contains (form.symm ▸ .reference name (.local binder)) empty raw
    | generalizedLocal contains reference layout lookup cell descriptor fields instantiated path =>
      cases same_node contains
      rw [empty] at path
      cases path
      exact .generalizedLocal contains reference layout lookup cell descriptor fields instantiated (empty ▸ .coercionsNil)
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases same_node contains
      rw [empty] at raw
      exact .atomicFault contains (form.symm ▸ .reference name (.local binder)) empty raw
    | coercion contains _ failed =>
      cases same_node contains
      rw [empty] at failed
      cases failed
    | generalizedLocalRequirement contains reference layout lookup cell descriptor fields selection failed =>
      exact .generalizedLocalRequirement contains reference layout lookup cell descriptor fields selection failed
    | generalizedLocalCoercion contains _ _ _ _ _ _ _ failed =>
      cases same_node contains
      rw [empty] at failed
      cases failed

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
/-! This compiler fragment contains only original reads, literals and products.
Its independent Source derivation lifts structurally; every reached child heap
is passed directly and no execution relation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
open Core Frontend SourceInference Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)

private theorem literal_atomic {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

private theorem literal_coercions {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem literal_nonlocal {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    ∀ name binder, node.form ≠ .reference name (.local binder) := by
  cases literal with
  | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
  | resolvedWord form _ | resolvedInteger form _ => intros; simp [form]

theorem exact_trace {values : SourceCoreCompatibleValues.Context}
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {solved : List SolvedRequirement} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Certificate readFuel values invocation.source context solved reasonAt scope id lowered)
    (unique : NodeOccurrencesUnique invocation.source) :
    ∀ {environment before outcome after},
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id outcome after →
      Staging.Recursive.Expression program registry invocation context environment before id (embed outcome) after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites with
  | literal _ receipt =>
    intro environment before outcome after trace
    obtain ⟨node, found, literal, _⟩ := receipt
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound found)
      (literal_atomic literal) (literal_coercions literal) (literal_nonlocal literal) trace
  | read receipt =>
    intro environment before outcome after trace
    obtain ⟨read, _, _⟩ := receipt
    exact CellAwareSourceReadLifting.read unique read.metadata.found read.form read.metadata.coercions trace
  | group metadata form innerFound sourceType child childSites ih =>
    intro environment before outcome after trace
    exact .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      (ih (CompatibleExpressionProducts.group_inv metadata form unique trace))
  | pair metadata form leftFound rightFound sourceType leftTree rightTree leftSites rightSites leftIH rightIH =>
    intro environment before outcome after trace
    have occurrence : Staging.Recursive.Occurrence invocation _ (.tuple [_, _]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    obtain ⟨sequence, children, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    cases packed with
    | values pack =>
      cases children with
      | values children =>
        cases children with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            cases pack with
            | cons tail =>
              cases tail
              exact .pair occurrence (leftIH (.value first)) (rightIH (.value second))
    | fault reason =>
      cases children with
      | fault failed =>
        cases failed with
        | head head => exact .pairLeftFault occurrence (leftIH (.fault head))
        | tail head tail =>
          cases tail with
          | head failed => exact .pairRightFault occurrence (leftIH (.value head)) (rightIH (.fault failed))
          | tail _ impossible => cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareReadEffects
/-! Completed ordinary reads retain every stored generalized declaration. Lazy
mapping initialization writes only its proven descriptor-free Source cell. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion
open GeneralizedLocalDescriptorHeap CellAwareScopeAuthority

/-- Mapping completion constructs only the actual raw source rule and its full
heap relation; callers choose their ordinary or staged outer constructor. -/
theorem Certificate.scoped_mapping_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    (declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep}
    {result : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        certificate.node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults (.value sourceValue) result ∧
      GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Effect instances mapping world heap store mapping world after finalStore := by
  have monomorphic := certificate.monomorphic
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
  obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
    GenericHeap.CellHeapRepresents.lookup_visible environments heaps lookup slot
  have sameCell := read.functional selectedRead
  subst selected
  have absent := locals.descriptor_empty_of_monomorphic heapTyped declaredScope lookup read monomorphic
  have represented := ordinaryCells.project represented absent
  cases emitted with
  | ordinary notMapping => exact False.elim (notMapping declaredMapping)
  | @mapping key value literal declaredType generated =>
    obtain ⟨empty, encodedType, quoted, emptyRep⟩ := generated.represents functions extension (.mapping .empty) mapping world
    rw [mapping_rename quoted] at evaluation
    have completed := read_completed (agrees nativeLookup) nativeRead quoted evaluation
    cases represented with
    | initialized payload =>
      dsimp only at cellType
      rcases completed with ⟨_, _, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
      · cases sameOptional
        subst result finalStore
        exact ⟨_, heap, form ▸ .local rfl lookup read rfl rfl,
          .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _, .refl _ _ _ _⟩
      · cases impossible
    | @uninitialized sourceType _ projected =>
      change sourceType = declared.scheme.body at cellType
      have same : encodedType = type := Except.ok.inj (emptyRep.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      rcases completed with ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, sameValue, originalWritten⟩
      · cases impossible
      · cases sameOptional
        subst result
        obtain ⟨after, written⟩ := writes_exists read (.mapping _ _ [])
        have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping _ _ []) empty type :=
          cellType.symm ▸ emptyRep
        obtain ⟨updated, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized ordinaryCells reference read absent cellPayload written
        have sameStore := Option.some.inj (nativeWritten.symm.trans originalWritten)
        cases sameStore
        exact ⟨_, after, form ▸ .localEmptyMapping rfl lookup read rfl (cellType.trans declaredType) rfl written,
          .value (.compatible (cellType ▸ occurrence) cellPayload), finalHeaps, frame, .of_write written,
          .write_ordinary heaps.injective read absent reference written nativeWritten⟩

/-- Every completed accepted local read determines its independent source outcome. -/
theorem Certificate.scoped_completed_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Effect instances mapping world heap store mapping world after finalStore := by
  by_cases declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value
  · obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata, effect⟩ :=
      certificate.scoped_mapping_completed functions extension ordinaryCells program sourceContext evidence binding declaredMapping
        environments heaps heapTyped locals agrees evaluation
    refine ⟨.value sourceValue, after, .value (.intro (middle := after) (raw := sourceValue) (lookupExpression?_sound certificate.metadata.found) ?_ ?_),
      represented, finalHeaps, frame, metadata, effect⟩
    · simpa only [certificate.metadata.requirements, certificate.metadata.coercions] using raw
    · rw [certificate.metadata.coercions]; exact .nil
  · have monomorphic := certificate.monomorphic
    rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
    rcases binding with ⟨declaredScope, occurrence⟩
    dsimp only at *
    cases emitted with
    | mapping declaredType generated => exact False.elim (declaredMapping ⟨_, _, declaredType⟩)
    | ordinary _ =>
      obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
      obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
        GenericHeap.CellHeapRepresents.lookup_visible environments heaps lookup slot
      have sameCell := read.functional selectedRead
      subst selected
      have absent := locals.descriptor_empty_of_monomorphic heapTyped declaredScope lookup read monomorphic
      have represented := ordinaryCells.project represented absent
      have ordinary := represented.ordinary
      have result := ordinary_completed (agrees nativeLookup) nativeRead evaluation
      have contains := lookupExpression?_sound metadata.found
      cases represented with
      | @initialized sourceType _ sourceValue nativeValue payload =>
        dsimp only at cellType
        rcases result with ⟨_, native, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
        · cases sameOptional
          subst value finalStore
          refine ⟨.value _, heap, .value (.intro (middle := heap) (raw := sourceValue) contains ?_ ?_),
            .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _, .refl _ _ _ _⟩
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read ordinary rfl
          · rw [metadata.coercions]; exact .nil
        · cases impossible
      | uninitialized projected =>
        dsimp only at cellType
        rcases result with ⟨_, _, impossible, _⟩ | ⟨_, _, _, sameValue, sameStore⟩
        · cases impossible
        · subst value finalStore
          refine ⟨.fault (.uninitializedLocation location), heap, .fault (.form contains ?_),
            .fault (uninitialized location _ ⟨contains, form, declaredScope, occurrence, lookup, read,
              cellType, ordinary, rfl, by simpa only [cellType] using declaredMapping⟩), heaps, .refl _ _, .refl _, .refl _ _ _ _⟩
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read ordinary rfl (by simpa only [cellType] using declaredMapping)

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Certificate.scoped_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Effect instances mapping world heap store mapping world after finalStore := by
  exact certificate.scoped_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
    environments heaps heapTyped locals agrees (fun location _ _ => uninitialized location) evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareReadMeaningEffects
/-! Both directions of accepted ordinary reads preserve the real mixed heap.
Native completion is assembled from the selected cell and literal code; the
independent Source trace is then identified by local read uniqueness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

theorem Certificate.scoped_preserves_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  obtain ⟨value, finalStore, evaluation⟩ := certificate.cell_native_terminates functions extension ordinaryCells
    binding environments heaps heapTyped locals agrees
  obtain ⟨actualOutcome, actualHeap, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
      environments heaps heapTyped locals agrees uninitialized evaluation
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have absent := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup read certificate.monomorphic
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read absent sourceTrace trace
  exact ⟨value, finalStore, evaluation, represented, finalHeaps, frame, metadata, effect⟩

theorem Certificate.scoped_reflects_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel context.checked registry functions) (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances))
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped sourceContext heap)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel context.checked registry functions) instances) mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  exact certificate.scoped_completed_with_diagnostics functions extension ordinaryCells program sourceContext evidence binding
    environments heaps heapTyped locals agrees uninitialized evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
/-! The actual finite ordinary expression tree completes in a mixed heap.
Every child keeps its original compiler receipt and actual reached state;
source uniqueness and descriptor effects are derived along the same tree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open Staging.Recursive.Lifting (embed)
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances))
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel (.initial checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include extension ordinaryCells uninitialized semantic unique selectedBodies runtime covers in
theorem completes {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Certificate readFuel (.initial checked) invocation.source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store : Store} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual) :
    ∃ size outcome after value finalStore,
      Staging.Recursive.Size.Expression program registry size invocation context environment before id (embed outcome) after ∧
      Evaluates actual store (lowered.expression.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world node.type lowered.type faults (embed outcome) value ∧
      GenericHeap.CellHeapRepresents cells mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context environment before id otherOutcome otherHeap →
        otherOutcome = embed outcome ∧ otherHeap = after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites generalizing node before store actual embedding with
  | literal _ receipt =>
    obtain ⟨other, otherFound, literal, _selected⟩ := receipt
    cases Option.some.inj (otherFound.symm.trans found)
    have valid := CompatibleExpressionTypedLiteralEvidence.of_typed unique found typed runtime.requirements.idsUnique covers
    obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
      literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
        environment before mapping world actual store embedding
    have staged : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before _ (.value sourceValue) before :=
      .atomicValue (lookupExpression?_sound found) (CellAwareSelectedLiteralBounds.literal_atomic_staged literal)
        (CellAwareSelectedLiteralBounds.literal_coercions literal)
        (by simpa only [CellAwareSelectedLiteralBounds.literal_coercions literal] using raw)
    refine ⟨_, .value sourceValue, before, _, store, staged, evaluated, .value represented,
      heaps, .refl _ _, .refl _, .refl _ _ _ _, ?_⟩
    intro otherSize outcome after trace
    cases outcome with
    | value value =>
      have otherRaw := CellAwareSelectedLiteralBounds.evaluation_raw unique (lookupExpression?_sound found)
        (CellAwareSelectedLiteralBounds.literal_atomic literal) (CellAwareSelectedLiteralBounds.literal_coercions literal)
        trace.sound.value_plain
      obtain ⟨rfl, rfl⟩ := CellAwareSelectedLiteralBounds.literal_form_unique literal otherRaw raw
      exact ⟨rfl, rfl⟩
    | fault failure =>
      cases failure with
      | semantic reason => exact False.elim (CellAwareSelectedLiteralBounds.literal_excludes_fault_with_evidence literal valid
          (CellAwareSelectedLiteralBounds.fault_raw unique (lookupExpression?_sound found)
            (CellAwareSelectedLiteralBounds.literal_atomic literal) (CellAwareSelectedLiteralBounds.literal_coercions literal)
            trace.sound.semanticFault_plain))
      | stage failedScope call reason => exact False.elim (CellAwareSelectedLiteralBounds.no_stage unique found literal trace)
  | @read readId readCode receipt =>
    have readReceipt := receipt
    obtain ⟨read, sameType, binding⟩ := receipt
    cases Option.some.inj (read.metadata.found.symm.trans found)
    obtain ⟨value, finalStore, evaluated⟩ := read.cell_native_terminates functions extension ordinaryCells
      binding environments heaps heapTyped locals agrees
    obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
      read.scoped_completed functions extension ordinaryCells program context invocation.evidence binding
        environments heaps heapTyped locals agrees (uninitialized _ _ _ readReceipt) evaluated
    obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
    have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead read.monomorphic
    have staged := CellAwareSelectedReadBounds.staged_of_read (registry := registry)
      read unique lookup sourceRead ordinary sourceTrace
    have staged' : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before readId (embed outcome) after := by
      cases outcome <;> exact staged
    have result : RecursiveStageMeaning.ResultRepresentsFor model mapping world read.node.type readCode.type faults (embed outcome) value := by
      simp only [SourceCoreCompatibleValues.Context.initial, sameType] at represented
      cases represented with
      | value payload => exact .value payload
      | fault matched => exact .fault (semantic _ _ matched)
    refine ⟨_, outcome, after, value, finalStore, staged', evaluated, result, finalHeaps, frame, metadata, effect, ?_⟩
    intro otherSize otherOutcome otherHeap trace
    have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
        Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before readId plainOutcome otherHeap ∧
        otherOutcome = embed plainOutcome := by
      cases otherOutcome with
      | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
      | fault failure => cases failure with
        | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
        | stage failedScope call reason => exact False.elim (CellAwareSelectedReadBounds.no_stage unique read.metadata.found read.form read.metadata.coercions trace)
    obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
    obtain ⟨rfl, rfl⟩ := CompatibleExpressionReads.source_outcome_unique unique
      (lookupExpression?_sound read.metadata.found) read.form read.metadata.coercions lookup sourceRead ordinary sourceTrace plainTrace
    exact ⟨outcomeEq, rfl⟩
  | @group id parent inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    cases Option.some.inj (metadata.found.symm.trans found)
    have childTyped := CellAwareStagedGroupBounds.child_typed metadata form innerFound unique typed
    obtain ⟨size, outcome, after, value, finalStore, trace, evaluated, represented, finalHeaps, frame, heapMetadata, effect, determines⟩ :=
      ih innerFound childTyped heaps heapTyped locals agrees
    refine ⟨_, outcome, after, value, finalStore,
      .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩ trace,
      evaluated, sourceType ▸ represented, finalHeaps, frame, heapMetadata, effect, ?_⟩
    intro otherSize otherOutcome otherHeap otherTrace
    obtain ⟨_, _, child⟩ := CellAwareStagedGroupBounds.source_group_inv unique metadata.found form otherTrace
    exact determines child
  | @pair id parent left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
    cases Option.some.inj (metadata.found.symm.trans found)
    obtain ⟨leftTyped, rightTyped⟩ := CellAwareSelectedPairBounds.child_typing metadata form leftFound rightFound unique typed
    have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [left,right]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    obtain ⟨firstSize, firstOutcome, middle, firstValue, middleStore, firstTrace, firstEval, firstRep,
      middleHeaps, firstFrame, firstMetadata, firstEffect, firstDetermines⟩ :=
      leftIH leftFound leftTyped heaps heapTyped locals agrees
    cases firstOutcome with
    | fault reason =>
      cases firstRep with
      | fault matched =>
        refine ⟨_, .fault reason, middle, _, middleStore, .pairLeftFault occurrence firstTrace, ?_,
          .fault matched, middleHeaps, firstFrame, firstMetadata, firstEffect, ?_⟩
        · rw [DataExpressionSequence.pair_rename]
          exact LocalSequence.pair_left_failure _ _ firstEval
        · intro otherSize otherOutcome otherHeap otherTrace
          have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
          cases children with
          | leftFault _ child => exact firstDetermines child
          | rightFault _ _ first _ | values _ _ first _ =>
            have impossible := (firstDetermines first).1
            cases impossible
    | value firstSource =>
      cases firstRep with
      | @value _ firstNative firstPayload =>
        have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies
          runtime covers locals heapTyped leftTyped firstTrace
        obtain ⟨secondSize, secondOutcome, after, secondValue, finalStore, secondTrace, secondEval, secondRep,
          finalHeaps, secondFrame, secondMetadata, secondEffect, secondDetermines⟩ :=
          rightIH rightFound rightTyped middleHeaps preserved.heap_typed (locals.mono firstMetadata)
            (agree_prefix agrees firstNative)
        cases secondOutcome with
        | fault reason =>
          cases secondRep with
          | fault matched =>
            refine ⟨_, .fault reason, after, _, finalStore, .pairRightFault occurrence firstTrace secondTrace, ?_,
              .fault matched, finalHeaps, firstFrame.trans secondFrame, firstMetadata.trans secondMetadata,
              firstEffect.trans secondEffect, ?_⟩
            · rw [DataExpressionSequence.pair_rename]
              rw [rename_prefix] at secondEval
              exact LocalSequence.pair_right_failure _ _ firstEval secondEval
            · intro otherSize otherOutcome otherHeap otherTrace
              have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
              cases children with
              | leftFault _ child => have impossible := (firstDetermines child).1; cases impossible
              | rightFault _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                exact secondDetermines second
              | values _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                have impossible := (secondDetermines second).1; cases impossible
        | value secondSource =>
          cases secondRep with
          | @value _ secondNative secondPayload =>
            refine ⟨_, .value (.product firstSource secondSource), after, _, finalStore,
              .pair occurrence firstTrace secondTrace, ?_, .value (by rw [sourceType]; exact .product firstPayload secondPayload),
              finalHeaps, firstFrame.trans secondFrame, firstMetadata.trans secondMetadata,
              firstEffect.trans secondEffect, ?_⟩
            · rw [DataExpressionSequence.pair_rename]
              rw [rename_prefix] at secondEval
              exact LocalSequence.pair_success _ _ firstEval secondEval
            · intro otherSize otherOutcome otherHeap otherTrace
              have children := CellAwareSelectedPairBounds.source_children unique metadata.found form otherTrace
              cases children with
              | leftFault _ child => have impossible := (firstDetermines child).1; cases impossible
              | rightFault _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                have impossible := (secondDetermines second).1; cases impossible
              | values _ _ first second =>
                obtain ⟨same, heapEq⟩ := firstDetermines first
                cases same; subst heapEq
                obtain ⟨same, heapEq⟩ := secondDetermines second
                cases same; subst heapEq
                exact ⟨rfl,rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
/-! The same reached owned pool returns through its saved physical caller
while ordinary and generalized Source cells retain their respective relations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open CallableIndexedOwnedBodyRestoration

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}
  (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}

/-- Actual frame restoration uses the selected saved row, preserving every
record produced by the body and the exact completed Source heap. -/
theorem restore_return {next : NativeFrame}
    (heaps : GenericHeap.CellHeapRepresents cells body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) :
    GenericHeap.CellHeapRepresents cells body.mapping body.world body.heap
      (finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping
      (finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost
      (finalIndex (body := body) saved selected).store ∧
    Relates saved (returned saved reached selected) := by
  let row := saved.rows selected
  obtain ⟨finalHeaps, finalFrame, finalCell⟩ := CellAwareBodyFrames.restore (next := next)
    (CallableIndexedAmbient.frame_registered compiled.indexed) row.authority.unmapped row.authority.typed
    row.authority.frame heaps worlds (by simp only [row.frame_eq]; exact frame)
  rw [row.frame_eq] at finalHeaps finalFrame finalCell
  exact ⟨finalHeaps, finalFrame, finalCell, returned_from_saved saved reached selected related⟩

include reached in
/-- Descriptor payloads survive the concrete restore write; administrative
preservation alone is not used to claim equality of mapped Source cells. -/
theorem restored_effect
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel compiled.indexed.layouts.definitions)
    (effect : CellAwareScopeAuthority.Effect instances caller.mapping caller.world caller.heap caller.store
      body.mapping body.world body.heap body.store) :
    CellAwareScopeAuthority.Effect instances caller.mapping caller.world caller.heap caller.store
      body.mapping body.world body.heap (finalIndex (body := body) saved selected).store := by
  have unmapped : keys[selected.val].frameLocation ∉ body.mapping := by
    have absent := (reached.rows selected).authority.unmapped
    simp only [(reached.rows selected).frame_eq] at absent
    exact absent
  exact effect.trans (.set_unmapped body.store
    (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current) unmapped)

end Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
/-! A bounded source scanner for lexical generalized declarations followed by
an actual returned expression. Every declared descriptor retains its exact
compiler catalog binding. The ordinary statement scanner is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

/-- These are decidable observations of one actual catalog at the source site.
The initializer search and binder lookup remain separate compiler actions. -/
structure Site (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (binder : TypedBinder) (initializer : ExpressionId) where
  binding : Binding
  initial : Binding
  located : locals.binding caller binder.id = .ok binding
  selected : locals.bindings.find? (fun entry =>
    decide (entry.caller = caller ∧ entry.initializer = initializer)) = some initial
  selectedBinder : initial.binder.id = binder.id
  bindingCaller : binding.caller = caller
  bindingInitializer : binding.initializer = initializer
  bindingMetadata : binding.binder.applySubstitution active = binder
  bindingSource : binding.source.applySubstitution active = source

def site? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (binder : TypedBinder) (initializer : ExpressionId) :
    Option (Site locals caller active source binder initializer) :=
  match located : locals.binding caller binder.id with
  | .error _ => none
  | .ok binding =>
    match selected : locals.bindings.find? (fun entry =>
        decide (entry.caller = caller ∧ entry.initializer = initializer)) with
    | none => none
    | some initial =>
      if selectedBinder : initial.binder.id = binder.id then
        if bindingCaller : binding.caller = caller then
          if bindingInitializer : binding.initializer = initializer then
            if bindingMetadata : binding.binder.applySubstitution active = binder then
              if bindingSource : binding.source.applySubstitution active = source then
                some ⟨binding, initial, located, selected, selectedBinder, bindingCaller,
                  bindingInitializer, bindingMetadata, bindingSource⟩
              else none
            else none
          else none
        else none
      else none

inductive Scan (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | returning {mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected mode (id :: rest)
  | tail {id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected true [id]
  | generalizedInitialized {mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

def scan? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan locals caller active source approved expected mode statements))
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt (some value) =>
        if sourceType : node.type = expected then
          match valueFound : source.lookupExpression? value with
          | none => none
          | some valueNode =>
            if valueType : valueNode.type = expected then do
              let ⟨approved⟩ ← expression value
              pure ⟨.returning rest found form sourceType valueFound valueType approved⟩
            else none
        else none
      | .expression value false =>
        match _modeEq : mode, _restEq : rest with
        | true, [] =>
          if sourceType : node.type = expected then
            match valueFound : source.lookupExpression? value with
            | none => none
            | some valueNode =>
              if valueType : valueNode.type = expected then do
                let ⟨approved⟩ ← expression value
                pure ⟨.tail found form sourceType valueFound valueType approved⟩
              else none
          else none
        | _, _ => none
      | .letDecl binder (some initializer) =>
        if sourceType : node.type = .unit then
          if polymorphic : binder.scheme.quantified ≠ [] then
            if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
              if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                  (fun actual => decide (actual.id = binder.id)) = [binder] then
                match initializerFound : source.lookupExpression? initializer with
                | none => none
                | some initializerNode =>
                  match initializerForm : initializerNode.form with
                  | .lambda _parameters _result _body =>
                    if valueType : initializerNode.type = binder.scheme.body then
                      if requirements : initializerNode.requirements = [] then
                        if coercions : initializerNode.coercions = [] then do
                          let site ← site? locals caller active source binder initializer
                          let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                          pure ⟨.generalizedInitialized found form sourceType declaration polymorphic ordinary initializerFound
                            initializerForm valueType requirements coercions site remaining⟩
                        else none
                      else none
                    else none
                  | _ => none
              else none
            else none
          else none
        else none
      | _ => none

inductive Syntax (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    SourceSemantics.Context → Bool → List StatementId → Prop where
  | returning {context mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | tail {context id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context true [id]
  | generalizedInitialized {context nextContext mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Context extension and child typing come from the original source checker,
including its generalized declaration rule. -/
theorem Scan.syntax {locals caller active source approved expected mode statements}
    (scan : Scan locals caller active source approved expected mode statements)
    (unique : NodeOccurrencesUnique source) {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    Syntax locals caller active source approved expected context mode statements := by
  induction scan generalizing control context final facts with
  | returning rest found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | returnValue actual =>
      exact .returning rest found form expressionFound valueType
        (by simpa only [result, valueType] using actual) value
  | tail found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual =>
      exact .tail found form expressionFound valueType (expression_at unique expressionFound actual) value
  | generalizedInitialized found form _ declaration polymorphic ordinary initializerFound initializerForm valueType requirements coercions site _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | letInitialized _ monomorphic _ => exact False.elim (polymorphic monomorphic)
    | letInitializedGeneralized _ _ _ _ extended =>
      exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound
        initializerForm valueType requirements coercions site (ih result tail)

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
/-! A selected named body keeps ordinary terminal expressions and generalized
native bundle declarations in one lexical tree. Actual marked allocations and
compiler candidate rows remain attached to each declaration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | returning {sourceContext scope mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {sourceContext scope id node expression expressionNode expected lowered}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .expression expression false)
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope true [id]
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | generalizedInitialized {sourceContext nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt prepared
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (context prepared named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      {captured : Expr}
      (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator prepared named))
        (source named) scope (fun index => index)
        (CellAwareGeneralizedSnapshotCode.snapshotInner lowered.type lowered.expression annotation.expression) =
          .ok captured)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (CellAwareGeneralizedSnapshotCode.snapshotSequence type captured body)

end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
/-! The native body collector follows the actual named compiler and its
marked lexical allocations. Source typing supplies context extension; the
accepted initializer supplies the complete ordered candidate bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)
open GeneralizedLocalInitializerCompilation (namedInputs)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

theorem scope_generalized {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context nextContext : SourceSemantics.Context} {binder : TypedBinder} (payload : Ty)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends source.owner context binder nextContext) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) nextContext := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    unfold SourceCoreDataPlaces.rootBinder at authentic
    by_cases owner : binder.id.owner ≠ source.owner
    · simp [owner, throw, bind, Except.bind] at authentic
    · cases quantified : binder.scheme.quantified with
      | nil => exact False.elim (polymorphic quantified)
      | cons first rest => simp [owner, declaration, quantified, throw, bind, Except.bind] at authentic
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

/-- Only finite static expression and candidate profiles are inputs. All
compiler actions and native child typing are recovered from the accepted body. -/
theorem collected
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (expressionPolicy : policy.lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
        ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
        diagnostics (context prepared named) prepared.base.callableContext none none)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (profiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [],
        Nonempty (GeneralizedLocalInitializerPackets.BindingProfile
          (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
            (context prepared named) scope initializer reasonAt) site.binding candidate))
    (bodyProfiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
        candidate.source initializer))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareSourceBodyAdmission.Syntax prepared.base.locals named.signature.key []
      (source named) approved expected sourceContext mode statements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    {fuel : Nat} {type : Ty} {code : Expr} {escaped : Word} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope statements
      type reasonAt mode escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    CellAwareNativeBodyTree.Tree prepared named compiled certificates administrative reasonAt
      sourceContext scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | @returning sourceContext mode id node expression expressionNode rest found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .returning rest found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @tail sourceContext id node expression expressionNode found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .tail found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @generalizedInitialized sourceContext nextContext mode id node binder initializer initializerNode parameters result body rest found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      have generalizedBinder : binder.scheme.quantified.isEmpty = false := by
        cases quantified : binder.scheme.quantified with
        | nil => exact absurd quantified polymorphic
        | cons _ _ => rfl
      simp only [generalizedBinder, Bool.false_eq_true, ↓reduceIte, SourceCoreSourceCells.letInitializedSnapshot,
        allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      obtain ⟨captured, copied, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have actualGenerated := expressionPolicy ▸ generated
      obtain ⟨childFuel, fuelEq, binding, located, ⟨initial⟩⟩ :=
        GeneralizedLocalInitializerCompilation.of_named_contextual compiled record
          initializerFound initializerForm site.selected actualGenerated
      have sameBinding : binding = site.binding := by
        rw [site.selectedBinder] at located
        exact Except.ok.inj (located.symm.trans site.located)
      subst binding
      subst fuel
      obtain ⟨initial⟩ := GeneralizedLocalInitializerPackets.of_receipt prepared initial
        (profiles site childFuel) (bodyProfiles site childFuel) rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨⟨_, childTyped⟩, tailTyped⟩ := CellAwareGeneralizedSnapshotTyping.snapshot_children allocation annotation
        same copied (fun _ _ _ found => CellAwareGeneralizedSnapshotTyping.scope_cell found) nativeTyped
      have tail := ih
        (scope_generalized lowered.type declarations declaration polymorphic extended)
        generatedTail tailTyped
      exact .generalizedInitialized found form declaration polymorphic extended ordinary
        initializerFound initializerForm valueType requirements coercions site initial
        (initial.typed childTyped) allocation annotation same copied tail
end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol
/-! Match prefixes allocate ordinary cells while retaining generalized cells.
The existing prefix proofs carry this concrete effect in their protocol relation;
the underlying protected state and its observation are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol
open Core Frontend SourceInference GeneralHeap CallableIndexedHistory
open ProtectedStateTransition
universe u v

variable {Records : Type v} {definitions : DataEnvironment}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions)
    (protocol : Protocol.{u, v} Records)

/-- Every relation edge retains the actual mapped descriptor rows. -/
def withEffects : Protocol.{u, v} Records where
  State := protocol.State
  records := protocol.records
  Relates := fun {initial reached} first last =>
    protocol.Relates first last ∧ CellAwareScopeAuthority.Effect instances
      initial.mapping initial.world initial.heap initial.store
      reached.mapping reached.world reached.heap reached.store
  refl := fun {_index} state => ⟨protocol.refl state, .refl _ _ _ _⟩
  trans := fun first second => ⟨protocol.trans first.1 second.1, first.2.trans second.2⟩

def bindings (original : Bindings protocol) : Bindings (withEffects instances protocol) where
  prepend := original.prepend
  prepend_related := fun state id type value =>
    ⟨original.prepend_related state id type value, .refl _ _ _ _⟩
  prepend_records := original.prepend_records
  restore := original.restore
  restore_related := fun state => ⟨original.restore_related state, .refl _ _ _ _⟩
  restore_records := original.restore_records

/-- The real allocator appends its snapshot, marker and payload. This proves
descriptor retention from the actual operation, without a separate effect law. -/
def producer {catalog : SourceCoreDataCatalog.Catalog}
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {cells : GenericHeap.CellModel definitions}
    (original : CellAllocation.Producer (catalog := catalog) protocol layouts frame cells) :
    CellAllocation.Producer (catalog := catalog) (withEffects instances protocol) layouts frame cells where
  Ready := original.Ready
  complete := by
    intro owner active request globals allocate allocation annotation same nativeDefinitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, captureTyped, evaluated, finalHeaps, finalReference, preserved, final, related⟩ :=
      original.complete allocation annotation same nativeDefinitions registered environments agrees heaps
        reference read payloadAt cell allocated initial ready
    refine ⟨captured, captures, captureTyped, evaluated, finalHeaps, finalReference, preserved,
      final, related, ?_⟩
    exact CellAwareScopeAuthority.Effect.append _ _ allocated.metadata ⟨_, rfl⟩ ⟨_, rfl⟩

/-- Forget the additional relation component only after the caller has retained
its concrete effect and the same reached protected state. -/
def forgetReturn {scope canonical reachedScope reachedCanonical}
    (receipt : ReturnTo (withEffects instances protocol) scope canonical reachedScope reachedCanonical) :
    ReturnTo protocol scope canonical reachedScope reachedCanonical where
  restore := receipt.restore
  related := fun state => (receipt.related state).1
  records_eq := receipt.records_eq

end Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
/-! The actual selected match prefix retains every generalized descriptor row.
The existing typed selection proof runs over a protocol whose relation records
its real allocation effects, and returns the same original protected state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix CallableIndexedHistory
universe u v

theorem selected_with_effect
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) ∧
        CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalAgreement, finalTyped, finalReference, finalRead, finalUnmapped,
    canonicalPrefix, continuation, final, related, ⟨returnTo⟩⟩ :=
      CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_cells_sized_with_literals
        certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid ordinaryCells
        (CellAwareMatchPrefixProtocol.withEffects instances protocol)
        (CellAwareMatchPrefixProtocol.producer instances protocol producer)
        (CellAwareMatchPrefixProtocol.bindings instances protocol stateBindings)
        definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped
        reference read unmapped evaluated initial readyAt selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalAgreement, finalTyped, finalReference, finalRead, finalUnmapped,
    canonicalPrefix, continuation, final, related.1,
    ⟨CellAwareMatchPrefixProtocol.forgetReturn instances protocol returnTo⟩, related.2⟩

theorem success_with_effect
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) ∧
        CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration, effect⟩ :=
    selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid instances ordinaryCells protocol producer stateBindings definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
/-! The actual ordinary-read terminal body completes in a mixed heap.
Its Source trace, native result and descriptor-preserving effect are constructed
from the literal compiler receipts without a body execution hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (ResultRepresents control)
open CallableIndexedOwnedAdmittedStagedTerminalBody (terminal_evaluates body_result)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances))
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy} {fuel readFuel : Nat}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {nativeType : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {body : Expr}
  (receipt : Receipt policy fuel invocation.source scope expression statements nativeType reasonAt fellThrough escaped body)
  {solved : List SolvedRequirement}
  (certificate : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel (.initial checked)
    invocation.source context solved reasonAt scope expression receipt.child)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? expression = some node)
  (unique : NodeOccurrencesUnique invocation.source)
  (typed : ExpressionHasType invocation.source context expression node.type)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {embedding : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
    administrative scope environment canonical ambient.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
    mapping world before store)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree embedding canonical actual)
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
theorem completes :
    ∃ size sourceOutcome after value finalStore,
      Staging.Recursive.Size.Statements program registry size invocation context environment before statements context
        (control (Staging.Recursive.Lifting.embed sourceOutcome)) after ∧
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults (Staging.Recursive.Lifting.embed sourceOutcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context environment before expression otherOutcome otherHeap →
        otherOutcome = Staging.Recursive.Lifting.embed sourceOutcome ∧ otherHeap = after := by
  obtain ⟨size, outcome, after, childValue, finalStore, staged, evaluated, represented,
      finalHeaps, preserved, metadata, effect, determines⟩ :=
    CellAwareReadProductCompletion.completes functions extension ordinaryCells uninitialized semantic unique
      (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) runtime covers certificate found typed environments heaps heapTyped locals agrees
  have flow : ∃ flowValue,
      Evaluates actual store ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename embedding)
        flowValue finalStore ∧
      ResultRepresents (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type receipt.child.type faults (Staging.Recursive.Lifting.embed outcome) flowValue := by
    rw [LoopRenaming.returnValue]
    cases outcome with
    | value value =>
      cases represented with
      | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluated, .returned payload⟩
    | fault reason =>
      cases represented with
      | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluated, .fault matched⟩
  obtain ⟨flowValue, flow, flowRep⟩ := flow
  obtain ⟨value, completed, resultRep⟩ := terminal_evaluates flowRep flow escaped
    (fallback := (CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename embedding)
  refine ⟨_, outcome, after, value, finalStore, (receipt.head invocation rfl).trace staged, ?_, ?_,
    finalHeaps, preserved, metadata, effect, determines⟩
  · rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt embedding]
    exact completed
  · simpa only [receipt.sameType] using resultRep

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
theorem reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (body.rename embedding) value finalStore) :
    ∃ size sourceOutcome after,
      Staging.Recursive.Size.Statements program registry size invocation context environment before statements context
        (control (Staging.Recursive.Lifting.embed sourceOutcome)) after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults (Staging.Recursive.Lifting.embed sourceOutcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨size, sourceOutcome, after, native, reached, trace, evaluated, represented, finalHeaps, frame, metadata, effect, _⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt certificate found unique
      typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨size, sourceOutcome, after, trace, represented, finalHeaps, frame, metadata, effect⟩

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult node.type bodyOutcome outcome) :
    ∃ value finalStore,
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨childSize, childOutcome, _, _, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique (receipt.head invocation rfl) trace
  have sameOutcome := CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  obtain ⟨_, sourceOutcome, actualAfter, value, finalStore, _, evaluated, represented,
      finalHeaps, frame, metadata, effect, determines⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt certificate found unique
      typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl,rfl⟩ := determines child
  exact ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareTerminalReadCompletion
/-! The actual ordinary-read terminal body completes in a mixed heap.
Its Source trace, native result and descriptor-preserving effect are constructed
from the literal compiler receipts without a body execution hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalReadCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (ResultRepresents control)
open CallableIndexedOwnedAdmittedStagedTerminalBody (terminal_evaluates body_result)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances))
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy} {fuel readFuel : Nat}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {nativeType : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {body : Expr}
  (receipt : Receipt policy fuel invocation.source scope expression statements nativeType reasonAt fellThrough escaped body)
  (read : CompatibleExpressionReads.LoweredRead readFuel (.initial checked)
    invocation.source context reasonAt scope expression receipt.child)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? expression = some node)
  (unique : NodeOccurrencesUnique invocation.source)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {embedding : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
    administrative scope environment canonical ambient.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
    mapping world before store)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree embedding canonical actual)
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt expression))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
theorem completes :
    ∃ sourceOutcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before
        expression sourceOutcome after ∧
      Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []])
        invocation context environment before statements context
        (control (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f))) after ∧
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults
        (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨certificate, sameChild, binding⟩ := read
  have sameNode := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨childValue, finalStore, evaluated⟩ := certificate.cell_native_terminates functions extension ordinaryCells
    binding environments heaps heapTyped locals agrees
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, preserved, metadata, effect⟩ :=
    certificate.scoped_completed functions extension ordinaryCells program context invocation.evidence binding
      environments heaps heapTyped locals agrees uninitialized evaluated
  obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead certificate.monomorphic
  have staged := CellAwareSelectedReadBounds.staged_of_read (registry := registry)
    certificate unique lookup sourceRead ordinary sourceTrace
  have flow : ∃ flowValue,
      Evaluates actual store ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename embedding)
        flowValue finalStore ∧
      ResultRepresents (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type receipt.child.type faults
        (match outcome with | .value v => .value v | .fault f => .fault (.semantic f)) flowValue := by
    rw [LoopRenaming.returnValue]
    have evaluation : Evaluates actual store (receipt.child.expression.rename embedding) childValue finalStore :=
      evaluated
    simp only [SourceCoreCompatibleValues.Context.initial, sameNode, sameChild] at represented
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluation, .returned payload⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluation, .fault (semantic _ _ matched)⟩
  obtain ⟨flowValue, flow, flowRep⟩ := flow
  obtain ⟨value, completed, resultRep⟩ := terminal_evaluates flowRep flow escaped
    (fallback := (CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename embedding)
  refine ⟨outcome, after, value, finalStore, sourceTrace, ?_, ?_, ?_,
    finalHeaps, preserved, metadata, effect⟩
  · cases outcome <;> exact (receipt.head invocation rfl).trace staged
  · rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt embedding]
    exact completed
  · cases outcome <;> simpa only [receipt.sameType] using resultRep

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
/-- Native completion reflects to the independently constructed original body
and exactly the same result, store and retained generalized rows. -/
theorem reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (body.rename embedding) value finalStore) :
    ∃ sourceOutcome : Dynamic.ExpressionOutcome, ∃ after,
      Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []])
        invocation context environment before statements context
        (control (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f))) after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults
        (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨sourceOutcome, after, native, reached, _, trace, evaluated, represented, finalHeaps, frame, metadata, effect⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt read found unique
      environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceOutcome, after, trace, represented, finalHeaps, frame, metadata, effect⟩

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
/-- An independent original terminal trace selects that same complete native
execution. Read uniqueness fixes both the Source result and reached heap. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult node.type bodyOutcome outcome) :
    ∃ value finalStore,
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  have originalRead := read
  obtain ⟨childSize, childOutcome, _, _, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique (receipt.head invocation rfl) trace
  have sameOutcome := CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  obtain ⟨certificate, _sameType, binding⟩ := read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before expression plainOutcome after ∧
      childOutcome = (match plainOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) := by
    cases childOutcome with
    | value value => exact ⟨.value value, .value child.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault child.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (CellAwareSelectedReadBounds.no_stage unique found (nodeEq ▸ certificate.form)
          (nodeEq ▸ certificate.metadata.coercions) child)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨sourceOutcome, actualAfter, value, finalStore, sourceTrace, _, evaluated, represented,
      finalHeaps, frame, metadata, effect⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt originalRead found unique
      environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead certificate.monomorphic
  obtain ⟨rfl, rfl⟩ := CompatibleExpressionReads.source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup sourceRead ordinary sourceTrace plainTrace
  exact ⟨value, finalStore, evaluated, outcomeEq.symm ▸ represented, finalHeaps, frame, metadata, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalReadCompletion
end
