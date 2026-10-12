import Solcore.Test.SourceCoreInitialLexicalFailureSeed
import Solcore.Test.SourceCoreInitialLexicalFailureStep
import Solcore.Test.SourceCoreInitialLexicalFailureHeap

/-! A first public failure returns the heap containing its newly allocated
absent local. That exact session and proved History then run identity(37),
which retains the absent cell while allocating its own initialized parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed
  next : ObservedContinuation first

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let next ← observeContinuation first
  return ⟨first, next⟩

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
    let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
    ∃ initial : RetainedState support sequence.first.returned [],
    ∃ final : RetainedState support sequence.next.completion.session [],
    ∃ location parameterLocation,
      Dynamic.Heap.Allocates ⟨[]⟩ .word none location initial.heap ∧
      Dynamic.Heap.Reads initial.heap location {type := .word, value := none} ∧
      Dynamic.Heap.Allocates initial.heap .word (some (.word seed)) parameterLocation final.heap ∧
      Dynamic.Heap.Reads final.heap location {type := .word, value := none} ∧
      SourceCall support support.failedHeader.header failedScope ⟨[]⟩ []
        (.fault (.semantic (.uninitializedLocation location))) initial.heap ∧
      SourceCall support support.identityHeader.header identityScope initial.heap [.word seed]
        (.value (.word seed)) final.heap

/-- Every semantic premise is produced from this accepted program and its
actual public events, including the first failed call's retained heap. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning failedStages identityStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed failedStages identityStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
  let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
  obtain ⟨initial, failure, failedCall⟩ := first_meaning support failedStages sequence.first
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := failedCall
  obtain ⟨location, failureEq, allocated, absent⟩ := support.failedHeader.failed_heap sourceAt applied
  obtain ⟨final, identityCall⟩ := initial.identity sequence.next identityScope
  obtain ⟨identityD, identityGlobal, identitySize, identityAt, identityApplied⟩ := identityCall
  obtain ⟨parameterLocation, parameterAllocated⟩ := support.identityHeader.identity_heap identityAt identityApplied
  refine ⟨support, initial, final, location, parameterLocation, allocated, absent,
    parameterAllocated, parameterAllocated.preserves_read absent, ?_, ?_⟩
  · exact ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  · exact ⟨identityD, identityGlobal, identitySize, identityAt, identityApplied⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed failedStages identityStages sequence receiver
  IO.println "Actual initial uninitialized failure: absent local retained; same returned session runs identity(37), Source traces and histories proved"

end Tests.SourceCoreInitialLexicalFailure
