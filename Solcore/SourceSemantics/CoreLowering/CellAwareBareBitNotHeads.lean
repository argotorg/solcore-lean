import Solcore.SourceSemantics.CoreLowering.CompatibleCellBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.Staging.RecursiveBareBitNot
import Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation

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
