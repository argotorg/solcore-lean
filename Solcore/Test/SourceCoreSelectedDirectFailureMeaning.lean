import Solcore.Test.SourceCoreSelectedLexicalFailureMeaning
import Solcore.Test.SourceCoreDirectFailurePublicExecution
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionDirectFailures

/-! The existing failed function is issued as a real retained handle. Its
packed failure and the later identity call keep the same complete history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First first_call eligible_row header_of_member header_types)
open Tests.SourceCoreDirectFailure (ObservedNamed ObservedFailure ObservedSuccess issuanceFuel failureOptions)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Profiled fixture.recipe}

theorem remember_named {stages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} (before : FirstMeaning issued stages first)
    (call : ObservedNamed first.returned observed.failedRow.row.key) :
    ∃ (entry : Entry) (global : Dynamic.GlobalFunction) (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment),
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      entry.source = .global global ∧ NamedSourceAt before.initial.header rawD global ∧
      ∃ next : issued.toIssued.State before.initial.header call.completion.session [entry],
        next.heap = before.after.heap := by
  obtain ⟨input, packet, member, sameHeader⟩ := issued.catalog.rows.mem_headers before.initial.header
    before.initial.start.selected.member
  have headerEq : packet.header = before.actual.header := sameHeader.trans before.headerEq
  have issuance : first.returned.NamedIssuedAt packet.header.named.signature.key issuanceFuel call.completion := by
    rw [headerEq, before.actual.key]
    exact call.issued
  obtain ⟨entry, entryType, source, handle, _handleType, next, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared
      before.after packet member issuance call.returned
  have sourceAt : NamedSourceAt before.initial.header input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)) :=
    sameHeader ▸ packet.sourceAt
  obtain ⟨facts, certificate⟩ := SelectedCompilationNamedArgumentRows.certified_at packet.sourceAt issued.support.bodyTyping
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned
  have bindingTypes : packet.header.types = [] := by
    rw [headerEq, header_types, before.actual.failed_inputs]
  have shape := certificate.callable_type
  change packet.header.named.specialized.function.type = _ at shape
  rw [← packet.sourceAt.frame.result, bindingTypes, headerEq, before.actual.failed_result_type] at shape
  exact ⟨entry, _, _, entryType.trans (by simpa only [headerEq, TypeSystem.Ty.productMany] using shape), handle, source, sourceAt, next, heap⟩

theorem invoke
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (actual : ActualHeader fixture observed.failedRow.row)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (entrySource : entry.source = .global global) (sourceAt : NamedSourceAt actual.header rawD global)
    (call : ObservedFailure session handle) (ready : session.ExportsReady)
    (invocation : Staging.Recursive.Scope) :
    ∃ (after : issued.toIssued.State anchor call.returned entries) (location : Dynamic.Location),
      Dynamic.Heap.Allocates before.heap .word none location after.heap ∧
      Dynamic.Heap.Reads after.heap location {type := .word, value := none} ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
      SourceCall anchor actual.header invocation before.heap [] (.fault (.semantic (.uninitializedLocation location))) after.heap ∧
      RecursiveNamedPublicPhysicalSessionState.PlainFault anchor actual.header invocation before.heap []
        (.uninitializedLocation location) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
        (.semantic (.uninitializedLocation location)) call.reason ∧
      ∃ checkpoint : SourceCoreExecution.Checkpoint artifact,
        session.startHandlePacked handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
        SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows anchor
          issued.initial issued.support.profile fixture.recipe entries (.semantic (.uninitializedLocation location)) checkpoint after.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have invoked : session.InvokeAt entry.handle .unit failureOptions (.ok (.failed call.reason call.returned)) := by
    rw [entryHandle]; exact call.executed
  obtain ⟨sources, packing, arity, failure, after, size, trace, plain, diagnostic⟩ :=
    issued.reflect_direct_failure_plain before entry member entryType input invoked invocation
  have noParameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  have sourceCount : sources.length = 0 := by
    have actualArity := entrySource ▸ arity
    have count := SelectedCompilationPackedNamedArguments.global_count actualArity
      issued.support.bodyTyping.function_ids sourceAt.frame.instantiated
    rw [← sourceAt.frame.parameters, noParameters] at count
    exact count.symm
  have noSources := List.eq_nil_of_length_eq_zero sourceCount
  subst sources
  have applied := entrySource ▸ trace
  obtain ⟨location, failureEq, allocated, absent⟩ := actual.failed_heap sourceAt applied
  obtain ⟨checkpoint, accepted, _resumed⟩ := invoked
  have forward := issued.forward_direct_failure before entry member entryType input accepted ready packing arity trace
  have sourceCall : SourceCall anchor actual.header invocation before.heap []
      (.fault (.semantic (.uninitializedLocation location))) after.heap :=
    ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  refine ⟨after, location, allocated, absent, arity, sourceCall, ?_, failureEq ▸ diagnostic,
    checkpoint, ?_, failureEq ▸ forward⟩
  · refine ⟨rawD, global, sourceAt, ?_⟩
    simpa only [entrySource, failureEq, SelectedCompilationCertifiedPublicSession.DirectFailureProjection,
      Staging.Recursive.callableEvidence] using plain
  · simpa only [entryHandle] using accepted

structure IdentityMeaning
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (stages : ObservedStages fixture observed.identityRow)
    (call : ObservedSuccess session observed.identityRow.row.key) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.identityRow.row.key [.word seed]
    runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : request.header = actual.header
  after : issued.toIssued.State anchor call.completion.session entries
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates before.heap .word (some (.word seed)) parameter after.heap
  trace : SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
    (.value (.word seed)) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainValue anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
    (.word seed) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
    issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe (.word seed)
    ⟨call.checkpoint, call.started⟩ after.heap

theorem identity
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (stages : ObservedStages fixture observed.identityRow)
    (call : ObservedSuccess session observed.identityRow.row.key) (ready : session.ExportsReady) :
    Nonempty (IdentityMeaning before stages call) := by
  let actualCall : RecursiveNamedPublicPhysicalSessionState.Call session observed.identityRow.row.key [.word seed] runOptions :=
    ⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before actualCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [← actualEq, actual.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have raw : request.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : request.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := issued.toIssued.reflect_scalar before (.word seed) actualCall
    call.returned request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall anchor request.header
      (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  exact ⟨⟨request, actual, actualEq.symm, after, parameter, allocated, sourceCall, sourceCall.value_plain,
    issued.toIssued.forward_scalar before (.word seed) actualCall.toStartedCall request
      inputs raw native ready sourceCall⟩⟩

end Tests.SourceCoreSelectedLexicalFailure
