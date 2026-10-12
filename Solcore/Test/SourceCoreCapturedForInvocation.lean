import Solcore.Test.SourceCoreCapturedForCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedPublicHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! Actual Bool/Word public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (flag : Bool) (argument : Core.Word) (stop : Bool) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [.bool flag, .word argument, .bool stop] outcome after

/-- Both the packed argument and callee meaning come from the original encoder
and current History. The returned state uses this call's exact public completion. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function (.product .bool (.product .word .bool)) .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    (parameters : function.parameters = [observed.running, observed.argument, observed.shape.stop])
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.product .bool (.product .word .bool)) .word)
    {flag : Bool} {argument : Core.Word} {stop : Bool} (call : ObservedInvocation publicSession handle flag argument stop)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source flag argument stop (.value (.word word)) after.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context (.product .bool (.product .word .bool))
      (.product (.bool flag) (.product (.word argument) (.bool stop))) (.product (.bool flag) (.product (.word argument) (.bool stop))) :=
    .product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.product
        (.data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
          ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩)
        (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
          ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, started, _parameterView, _resultView, succeeded,
      actualAt, packing, arity, trace, result, _related, retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectPackedPublicHistory.public_invoke_succeeded_function_tree
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.product (.bool flag) (.product (.word argument) (.bool stop))))
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function (.product .bool (.product .word .bool)) .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [.bool flag, .word argument, .bool stop] :=
    packing.injective_of_length_eq (.cons (.cons (.singleton (.bool stop)))) (by simpa [parameters] using arity)
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, sourcesEq, outcomeValue] using trace

end Tests.SourceCoreCapturedFor
