import Solcore.Test.SourceCoreSelectedDirectFailureMeaning

/-! The original lexical program preserves its real failure, retained handle,
second failure and scalar continuation through one selected public issuer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First FreshIdentity observeFreshIdentity)
open Tests.SourceCoreDirectFailure (ObservedSequence observeSequence failureOptions)
open SelectedCompilationCertifiedPublicSession (Profiled)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

private theorem failure_ready
    {artifact : SourceCoreExecution.Artifact} {session returned : SourceCoreExecution.Session artifact}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} {reason : Core.Word}
    {issued : Profiled fixture.recipe}
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries)
    (run : session.InvokeAt handle argument options (.ok (.failed reason returned)))
    (ready : session.ExportsReady) : returned.ExportsReady := by
  obtain ⟨checkpoint, started, resumed⟩ := run
  obtain ⟨indexedCheckpoint, atCheckpoint, actualStart⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession started
  obtain ⟨_actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (actualStart.initial_registry.exportsReady
      (state.atSession.exportsReady_iff.mp ready)))

structure RetainedSequenceMeaning (issued : Profiled fixture.recipe)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued failedStages sequence.first
  entry : Entry
  sourceType : entry.sourceType = .function .unit .word
  handle : entry.handle = sequence.named.handle
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0
  named : issued.toIssued.State first.initial.header sequence.named.completion.session [entry]
  namedHeap : named.heap = first.after.heap
  failed : issued.toIssued.State first.initial.header sequence.failed.returned [entry]
  location : Dynamic.Location
  allocated : Dynamic.Heap.Allocates named.heap .word none location failed.heap
  absent : Dynamic.Heap.Reads failed.heap location {type := .word, value := none}
  trace : SourceCall first.initial.header first.actual.header
    (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function) named.heap []
    (.fault (.semantic (.uninitializedLocation location))) failed.heap
  plain : PlainFault first.initial.header first.actual.header
    (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function) named.heap []
    (.uninitializedLocation location) failed.heap
  diagnostic : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults failed.receiving.result.diagnostics
    (.semantic (.uninitializedLocation location)) sequence.failed.reason
  checkpoint : SourceCoreExecution.Checkpoint sequence.first.artifact
  started : sequence.named.completion.session.startHandlePacked sequence.named.handle .unit
    failureOptions.inputValidationFuel = .ok checkpoint
  forward : SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows
    first.initial.header issued.initial issued.support.profile fixture.recipe [entry]
    (.semantic (.uninitializedLocation location)) checkpoint failed.heap
  identity : IdentityMeaning failed identityStages sequence.next
  firstKept : Dynamic.Heap.Reads identity.after.heap first.location {type := .word, value := none}
  secondKept : Dynamic.Heap.Reads identity.after.heap location {type := .word, value := none}

/-- Actual compiler profile and public receipts supply all body support and
registry preservation; no Source trace or completion callback is supplied. -/
theorem retained_sequence_meaning
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Profiled fixture.recipe,
      Nonempty (RetainedSequenceMeaning issued failedStages identityStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile failedStages sequence.first
  obtain ⟨entry, global, rawD, sourceType, handle, source, sourceAt, named, namedHeap⟩ :=
    remember_named first sequence.named
  have ready := sequence.named.issued.exportsReady sequence.first.returned_exportsReady
  obtain ⟨failed, location, allocated, absent, arity, trace, plain, diagnostic, checkpoint, started, forward⟩ :=
    invoke named first.actual entry (by simp) sourceType handle source (first.headerEq ▸ sourceAt)
      sequence.failed ready (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function)
  obtain ⟨after⟩ := identity failed identityStages sequence.next (failure_ready named sequence.failed.executed ready)
  exact ⟨issued, ⟨⟨first, entry, sourceType, handle, arity, named, namedHeap, failed, location,
    allocated, absent, trace, plain, diagnostic, checkpoint, started, forward, after,
    after.allocated.preserves_read (allocated.preserves_read (namedHeap.symm ▸ first.absent)),
    after.allocated.preserves_read absent⟩⟩⟩

theorem closed_outcomes
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (fresh : FreshIdentity fixture observed) :
    (∃ issued : Profiled fixture.recipe,
      Nonempty (RetainedSequenceMeaning issued failedStages identityStages sequence)) ∧
    (∃ issued : Profiled fixture.recipe, Nonempty (FreshMeaning issued identityStages fresh)) :=
  ⟨retained_sequence_meaning profile failedStages identityStages sequence, fresh_meaning profile identityStages fresh⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observeProfile fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  let fresh ← observeFreshIdentity fixture observed
  have _meaning := closed_outcomes profile failedStages identityStages sequence fresh
  IO.println "SELECTED_PROFILED_FAILURES_PASS: original checker1000/compiler100; initial fault; retained named handle; direct fault at output fuel0; identity37 keeps two absent cells and the handle; fresh identity37; exact Dynamic outcomes and forward bounds"

end Tests.SourceCoreSelectedLexicalFailure
