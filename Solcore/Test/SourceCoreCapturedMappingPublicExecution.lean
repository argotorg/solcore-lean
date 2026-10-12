import Solcore.Test.SourceCoreCapturedMappingInvocation
import Solcore.Test.SourceCoreCapturedMappingSeed
import Solcore.Test.SourceCoreCapturedMappingClosureShape

/-! Actual make(10) and two mapping-input calls share the exported closure
and successive public sessions. Each Source application retains the literal
ordered rows, current heap and authentic table at its own input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def firstArgument : List (Core.Word × Core.Word) :=
  [(Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 99),
   (Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 123)]

def secondArgument : List (Core.Word × Core.Word) :=
  [(Core.Word.ofNatModulo 2, Core.Word.ofNatModulo 456)]

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ObservedInvocation factory.completion.session factory.handle firstArgument
  firstValue : first.completion.value = .word seed
  second : ObservedInvocation first.completion.session factory.handle secondArgument
  secondValue : second.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeInvocation factory.completion.session factory.handle firstArgument
  if firstValue : first.completion.value = .word seed then
    let second ← observeInvocation first.completion.session factory.handle secondArgument
    if secondValue : second.completion.value = .word seed then
      return ⟨factory, first, firstValue, second, secondValue⟩
    else throw (IO.userError "second packed call changed its captured seed")
  else throw (IO.userError "first packed call returned its argument instead of its captured seed")

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (entry : Entry) (function : Dynamic.Closure),
      entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      entry.source = .closure function ∧ function.parameters = [observed.argument] ∧
      function.resultType = .word ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap

/-- The accepted checker/compiler and original public execution construct all
static supports, closure provenance and the three connected Source applications. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry
    (receiver.issued)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ :=
    first_meaning support stages sequence.factory
  obtain ⟨function, source, parameters, result⟩ := factoryTrace.make_closure
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType handle handleType
    sequence.first sequence.firstValue scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType handle handleType
    sequence.second sequence.secondValue scope
  exact ⟨support, entry, function, entryType, handle, source, parameters, result,
    initial, first, final, factoryTrace, firstTrace, finalTrace⟩

/-- The final consumer derives its initial receiver from the accepted compiler
and needs only observations of the three actual public calls. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ receiver, SequenceMeaning stages sequence receiver := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed stages sequence receiver⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual mapping closure reuse: duplicate ordered rows, captured results 10/10, Source applications and authentic receivers proved"

end Tests.SourceCoreCapturedMapping
