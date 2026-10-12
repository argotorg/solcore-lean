import Solcore.Test.SourceCoreDirectFailureInvocation
import Solcore.Test.SourceCoreDirectFailureSuccess
import Solcore.Test.SourceCoreInitialLexicalFailureHeap
/-! The first failed named run seeds the real heap. Named issuance then exposes
that same declared function, a direct packed call fails with output fuel zero,
and identity(37) succeeds in its returned session. Both absent locals survive.
The independently reflected direct Source fault also guarantees actual public
failure at every sufficient execution budget, for every output budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed
  named : ObservedNamed first.returned observed.failedRow.row.key
  failed : ObservedFailure named.completion.session named.handle
  next : ObservedSuccess failed.returned observed.identityRow.row.key

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let named ← observeNamed first.returned observed.failedRow.row.key
  let failed ← observeFailure named.completion.session named.handle
  let next ← observeSuccess failed.returned observed.identityRow.row.key
  pure ⟨first, named, failed, next⟩

theorem ObservedPublicRun.returned_exportsReady {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed) : first.returned.ExportsReady := by
  obtain ⟨_artifact, _session, checkpoint, _root, _world, _store, _native, _values,
      _opened, _prepared, atSession, atCheckpoint, started⟩ := first.start_receipt
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := first.executed
  have same : publicCheckpoint = first.checkpoint := Except.ok.inj (accepted.symm.trans first.started)
  subst publicCheckpoint
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (started.original.initial_registry.exportsReady (atSession.exportsReady_iff.mp ready)))

/-- All program, input, declared arity and reached-state conditions come from
this compiler and these real public events. No Source trace is a premise. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
      let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
      ∃ (initial : RetainedState support sequence.first.returned []) (entry : Entry)
        (issued : RetainedState support sequence.named.completion.session [entry])
        (failed : RetainedState support sequence.failed.returned [entry])
        (final : RetainedState support sequence.next.completion.session [entry])
        (firstLocation secondLocation parameterLocation : Dynamic.Location),
        entry.sourceType = .function .unit .word ∧ entry.handle = sequence.named.handle ∧
        RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
        Dynamic.Heap.Allocates ⟨[]⟩ .word none firstLocation initial.heap ∧ issued.heap = initial.heap ∧
        Dynamic.Heap.Allocates issued.heap .word none secondLocation failed.heap ∧
        Dynamic.Heap.Allocates failed.heap .word (some (.word seed)) parameterLocation final.heap ∧
        Dynamic.Heap.Reads final.heap firstLocation { type := .word, value := none } ∧
        Dynamic.Heap.Reads final.heap secondLocation { type := .word, value := none } ∧
        SourceCall support support.failedHeader.header failedScope ⟨[]⟩ []
          (.fault (.semantic (.uninitializedLocation firstLocation))) initial.heap ∧
        SourceCall support support.failedHeader.header failedScope issued.heap []
          (.fault (.semantic (.uninitializedLocation secondLocation))) failed.heap ∧
        SourceCall support support.identityHeader.header identityScope failed.heap [.word seed]
          (.value (.word seed)) final.heap ∧
        ∃ checkpoint : SourceCoreExecution.Checkpoint sequence.first.artifact,
          sequence.named.completion.session.startHandlePacked sequence.named.handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
          ForwardFailureAt support checkpoint [entry] (.semantic (.uninitializedLocation secondLocation)) failed.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed failedStages identityStages
    receiver.completion.result.context.registry receiver.issued
  let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
  let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
  obtain ⟨initial, firstFailure, firstCall⟩ := first_meaning support failedStages sequence.first
  obtain ⟨firstD, firstGlobal, firstSize, firstAt, firstTrace⟩ := firstCall
  obtain ⟨firstLocation, firstEq, firstAllocated, firstAbsent⟩ := support.failedHeader.failed_heap firstAt firstTrace
  obtain ⟨entry, global, entryType, entryHandle, entrySource, sourceAt, arity, issued, issuedHeap⟩ :=
    remember_named initial sequence.named
  have ready := sequence.named.issued.exportsReady sequence.first.returned_exportsReady
  obtain ⟨failed, secondFailure, failedCall, checkpoint, started, forward⟩ :=
    invoke issued entry (by simp) entryType entryHandle entrySource sourceAt sequence.failed ready failedScope
  obtain ⟨secondD, secondGlobal, secondSize, secondAt, secondTrace⟩ := failedCall
  obtain ⟨secondLocation, secondEq, secondAllocated, secondAbsent⟩ := support.failedHeader.failed_heap secondAt secondTrace
  obtain ⟨final, nextCall⟩ := failed.identity sequence.next identityScope
  obtain ⟨identityD, identityGlobal, identitySize, identityAt, identityTrace⟩ := nextCall
  obtain ⟨parameterLocation, parameterAllocated⟩ := support.identityHeader.identity_heap identityAt identityTrace
  have firstKept : Dynamic.Heap.Reads final.heap firstLocation { type := .word, value := none } :=
    parameterAllocated.preserves_read (secondAllocated.preserves_read (issuedHeap.symm ▸ firstAbsent))
  refine ⟨receiver, support, initial, entry, issued, failed, final, firstLocation, secondLocation, parameterLocation,
    entryType, entryHandle, arity, firstAllocated, issuedHeap, secondAllocated, parameterAllocated,
    firstKept, parameterAllocated.preserves_read secondAbsent, ?_, ?_, ?_, checkpoint, started, ?_⟩
  · exact ⟨firstD, firstGlobal, firstSize, firstAt, firstEq ▸ firstTrace⟩
  · exact ⟨secondD, secondGlobal, secondSize, secondAt, secondEq ▸ secondTrace⟩
  · exact ⟨identityD, identityGlobal, identitySize, identityAt, identityTrace⟩
  · exact secondEq ▸ forward

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed failedStages identityStages sequence
  IO.println "Actual direct named failure: output fuel0, Source arity and sufficient-fuel failure, two absent cells retained through identity37 proved"

end Tests.SourceCoreDirectFailure
