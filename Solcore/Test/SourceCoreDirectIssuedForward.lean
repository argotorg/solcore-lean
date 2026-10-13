import Solcore.Test.SourceCoreDirectIssuedPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectWordForward

/-! The actual two packed calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) (word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value} {word : Core.Word}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (_simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (call : ObservedInvocation publicSession handle argument)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source source word after) :
    ForwardWordAt support publicSession entries handle argument word after := by
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨size, trace⟩ := trace
  refine ⟨publicCheckpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectWordForward.forward_call support.program
    fixture.recipePrepared state entry member word entryType input
    (by simpa only [entryHandle] using accepted) (.singleton source) trace


def ForwardSequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named builtin : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function (.function .unit .word) .word ∧
      builtin.sourceType = .function .integer .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      builtin.handle = sequence.builtin.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      builtin.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ readState : RetainedState support sequence.read.completion.session [first, named],
      ∃ builtinState : RetainedState support sequence.builtin.completion.session [first, named, builtin],
      ∃ finalState : RetainedState support sequence.converted.completion.session [first, named, builtin],
        namedState.heap = firstState.heap ∧ builtinState.heap = readState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceInvocation support scope namedState.heap named.source first.source seed readState.heap ∧
        SourceInvocation support scope builtinState.heap builtin.source (.integer builtinArgument)
          builtinResult finalState.heap ∧
        ForwardWordAt support sequence.named.completion.session [first, named] sequence.named.handle
          (.function sequence.first.handle) seed readState.heap ∧
        ForwardWordAt support sequence.builtin.completion.session [first, named, builtin] sequence.builtin.handle
          (.integer builtinArgument) builtinResult finalState.heap

/-- The real named and builtin calls establish independent Source traces,
then prove public success for all sufficient fuel on those same checkpoints. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ForwardSequenceMeaning makeStages sequence receiver := by
  obtain ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace⟩ := sequence_meaning fixture observed extra admission makeStages readStages sequence receiver
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named]
      support.makeHeader.header.function.context (.function .unit .word)
      (.function sequence.first.handle) first.source := by
    simpa only [firstType, firstHandle] using
      (RecursiveNamedPublicFunctionHistoryInputs.Input.retained
        (context := support.makeHeader.header.function.context) first (by simp : first ∈ [first, named]))
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named, builtin]
      support.makeHeader.header.function.context .integer (.integer builtinArgument) (.integer builtinArgument) :=
    .data ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
      ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
  exact ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace,
    forward_word namedState named (by simp) namedType namedHandle input (.function sequence.first.handle)
      sequence.read readTrace,
    forward_word builtinState builtin (by simp) builtinType builtinHandle integerInput (.simple (.integer builtinArgument))
      sequence.converted finalTrace⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning : ∃ receiver : ObservedReceiver fixture observed, ForwardSequenceMeaning makeStages sequence receiver := by
    obtain ⟨receiver⟩ := initial_receiver fixture observed
    exact ⟨receiver, sequence_forward_meaning fixture observed extra admission makeStages readStages sequence receiver⟩
  IO.println "Actual direct named and builtin calls: Source reflection and public Word preservation with output fuel 1 proved"

end Tests.SourceCoreDirectIssued
