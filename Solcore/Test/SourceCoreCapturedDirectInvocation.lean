import Solcore.Test.SourceCoreCapturedDirectSequence
import Solcore.Test.SourceCoreCapturedReuseCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! A direct public invocation consumes the actual retained Source closure and
returns its existing history at the real completed session and captured heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source [] outcome after

theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    (parameters : function.parameters = [])
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit .word)
    (call : ObservedInvocation publicSession handle)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source (.value (.word word)) after.heap := by
  obtain ⟨nativeAt, heaps, stable, heapTyped, entriesAt⟩ := state.history.current
  obtain ⟨imported, represented, sourceTyped⟩ := entriesAt entry member
  rw [entryType, entryHandle] at imported
  rw [entryType, entrySource] at represented sourceTyped
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate
    support.makeHeader.header fixture.source_wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      support.makeHeader.header.function.context support.makeHeader.header.function.source := by
    rw [support.makeHeader.header.frame.context, support.makeHeader.header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  obtain ⟨checkpoint, actual, generation, value, finalStore, nativeResult, sourceSize, outcome,
      after, finalMap, finalWorld, started, succeeded, actualAt, projected, requested, _payloadType,
      trace, result⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.public_invoke_succeeded_reflects_unit
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (caller := state.caller) (stable := stable)
      (runtime := runtime) (heapTyped := heapTyped) (calleeTyped := sourceTyped)
      (calleeRelated := represented) (parameters := parameters) (heaps := heaps)
      (prepared := fixture.recipePrepared) (atRecipe := state.atRecipe) (nativeAt := nativeAt)
      (handleType := handleType) (imported := imported) state.atSession call.executed invocation
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  obtain ⟨reached, _related, retained⟩ := state.history.after_packed_success started succeeded result
  have registry := started.returned_registry succeeded
  rw [started.simple_registry .unit, state.registry] at registry
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, registry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, outcomeValue] using trace

end Tests.SourceCoreCapturedDirect
