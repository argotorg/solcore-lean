import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.Test.SourceCoreSelectedLexicalFailureProfile
import Solcore.Test.SourceCoreInitialLexicalFailureHeap

/-! The unchanged lexical program uses one automatically issued physical
session after its first failure, then continues with identity(37). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First FreshIdentity first_call original_first continuation_call first_returned_ready eligible_row header_of_member header_types)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) where
  initial : Initial issued.toIssued (first_call first)
  actual : ActualHeader fixture observed.failedRow.row
  headerEq : initial.header = actual.header
  after : issued.toIssued.State initial.header first.returned []
  location : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word none location after.heap
  absent : Dynamic.Heap.Reads after.heap location {type := .word, value := none}
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
    (.fault (.semantic (.uninitializedLocation location))) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainFault initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
    (.uninitializedLocation location) after.heap
  decoded : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
    (.semantic (.uninitializedLocation location)) first.reason
  forward : SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.semantic (.uninitializedLocation location)) (first_call first) after.heap

structure ContinuationMeaning {issued : Profiled fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    next.checkpoint before.after.session observed.identityRow.row.key [.word seed]
    runOptions.inputValidationFuel before.after.world before.after.store
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : request.header = actual.header
  after : issued.toIssued.State before.initial.header next.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates before.after.heap .word (some (.word seed)) parameter after.heap
  absent : Dynamic.Heap.Reads after.heap before.location {type := .word, value := none}
  trace : SourceCall before.initial.header request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
    (.value (.word seed)) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows before.initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) (continuation_call next).toStartedCall after.heap

structure FreshMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) where
  initial : Initial issued.toIssued fresh.call.toStartedCall
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : initial.header = actual.header
  after : issued.toIssued.State initial.header fresh.call.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word (some (.word seed)) parameter after.heap
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
    (.value (.word seed)) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainValue initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
    (.word seed) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) fresh.call.toStartedCall after.heap

theorem first_meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.failedRow
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile first.opened
    (first_call first) first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.failedRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [] initial.header.types := by
    rw [header_types, ← actualEq, actual.failed_inputs]
    exact .nil
  have simple : ∀ value ∈ ([] : List SourceCorePublicValues.Value), SourceCoreIndexedSession.SimplePublic value := by
    intro value member; cases member
  obtain ⟨failure, after, trace, plain, decoded⟩ := SelectedCompilationCertifiedPublicSession.Profiled.reflect_initial_failure_plain initial first.returned first.reason first.executed
    simple inputTypes .nil (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨location, failureEq, allocated, absent⟩ := actual.failed_heap
    (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
      (.fault (.semantic (.uninitializedLocation location))) after.heap :=
    ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, location, allocated, absent,
    sourceCall, (by simpa only [failureEq, RecursiveNamedPublicPhysicalSessionState.FailureProjection] using plain), failureEq ▸ decoded, SelectedCompilationCertifiedPublicSession.Profiled.forward_initial_failure initial simple inputTypes .nil sourceCall⟩⟩⟩

theorem continuation_meaning {issued : Profiled fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) :
    Nonempty (ContinuationMeaning before stages next) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before.after (continuation_call next).toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [← actualEq, actual.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have raw : request.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : request.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := issued.toIssued.reflect_scalar before.after (.word seed) (continuation_call next)
    next.returned request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall before.initial.header request.header
      (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  have ready : first.returned.ExportsReady := first_returned_ready first
  exact ⟨⟨request, actual, actualEq.symm, after, parameter, allocated,
    allocated.preserves_read before.absent, sourceCall,
    issued.toIssued.forward_scalar before.after (.word seed) (continuation_call next).toStartedCall request
      inputs raw native ready sourceCall⟩⟩

theorem fresh_meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FreshMeaning issued stages fresh) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile fresh.opened
    fresh.call.toStartedCall fresh.bootstrap fresh.fresh fresh.authority
    (show fresh.bootstrap.ReadyAt 100000 fresh.session from .single fresh.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [header_types, ← actualEq, actual.identity_inputs]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have simple : ∀ value ∈ [.word seed], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact .word seed
  have raw : initial.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : initial.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := initial.reflect_scalar (.word seed) fresh.returned simple inputTypes inputMeanings
    raw native (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, parameter, allocated, sourceCall, sourceCall.value_plain,
    initial.forward_scalar (.word seed) simple inputTypes inputMeanings raw native sourceCall⟩⟩⟩

end Tests.SourceCoreSelectedLexicalFailure
