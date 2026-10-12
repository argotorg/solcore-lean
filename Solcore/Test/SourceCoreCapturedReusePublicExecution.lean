import Solcore.Test.SourceCoreCapturedReuseSeed
import Solcore.Test.SourceCoreCapturedReuseMakeStep
import Solcore.Test.SourceCoreCapturedReuseReadStep

/-! The actual checked two-function program connects six public executions to
independent Source applications and reusable histories. Distinct captures are
read after another factory invocation, then the first capture is read again. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let makeScope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    let readScope := RecursiveStageRegistry.scope readStages.sidecar [] support.readHeader.header.function
    ∃ first second intervening : Entry,
      first.sourceType = .function .unit .word ∧ second.sourceType = .function .unit .word ∧
      intervening.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ second.handle = sequence.second.handle ∧
      intervening.handle = sequence.intervening.handle ∧ first.handle ≠ second.handle ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, second],
      ∃ firstReadState : RetainedState support sequence.readFirst.completion.session [first, second],
      ∃ interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening],
      ∃ secondReadState : RetainedState support sequence.readSecond.completion.session [first, second, intervening],
      ∃ finalState : RetainedState support sequence.readFirstAgain.completion.session [first, second, intervening],
        SourceCall support support.makeHeader.header makeScope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.makeHeader.header makeScope firstState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        SourceCall support support.readHeader.header readScope secondState.heap [first.source]
          (.value (.word seed)) firstReadState.heap ∧
        SourceCall support support.makeHeader.header makeScope firstReadState.heap [.word interveningSeed]
          (.value intervening.source) interveningState.heap ∧
        SourceCall support support.readHeader.header readScope interveningState.heap [second.source]
          (.value (.word secondSeed)) secondReadState.heap ∧
        SourceCall support support.readHeader.header readScope secondReadState.heap [first.source]
          (.value (.word seed)) finalState.heap

/-- Every static support and dynamic history is built from the actual checker,
compiler, public startups and public execution receipts of this fixture. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages readStages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let makeScope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  let readScope := RecursiveStageRegistry.scope readStages.sidecar [] support.readHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstState, firstTrace⟩ :=
    first_meaning extra support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondState, secondTrace⟩ :=
    firstState.make extra sequence.second makeScope
  obtain ⟨firstReadState, firstReadTrace⟩ := secondState.read first (by simp)
    firstType firstHandle sequence.readFirst sequence.firstValue readScope
  obtain ⟨intervening, interveningType, interveningHandle, interveningState, interveningTrace⟩ :=
    firstReadState.make extra sequence.intervening makeScope
  obtain ⟨secondReadState, secondReadTrace⟩ := interveningState.read second (by simp)
    secondType secondHandle sequence.readSecond sequence.secondValue readScope
  obtain ⟨finalState, finalTrace⟩ := secondReadState.read first (by simp)
    firstType firstHandle sequence.readFirstAgain sequence.firstValueAgain readScope
  refine ⟨support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, ?_, firstState, secondState, firstReadState,
    interveningState, secondReadState, finalState, firstTrace, secondTrace, firstReadTrace,
    interveningTrace, secondReadTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual captured closure reuse: six public calls, distinct captures 10/20, intervening make(30), Source Word results and retained histories proved"

end Tests.SourceCoreCapturedReuse
