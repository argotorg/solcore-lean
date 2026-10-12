import Solcore.Test.SourceCoreConstructorCallsIssuance
import Solcore.Test.SourceCoreConstructorCallsSelectionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev packedType : TypeSystem.Ty := TypeSystem.Ty.productMany [makerType, .word, closureType, convertType]
def packedSource (factory prior convert : Dynamic.Value) : Dynamic.Value :=
  .product factory (.product (.word secondSeed) (.product prior convert))

theorem construction_input {entries : List Entry} {context : SourceSemantics.Context}
    (factory prior convert : Entry) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {f p c : SourceCorePublicValues.Handle} (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context packedType
      (packedArgument f p c) (packedSource factory.source prior.source convert.source) := by
  have factoryInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) factory factoryMember
  have priorInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) prior priorMember
  have convertInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) convert convertMember
  rw [factoryType, factoryHandle] at factoryInput
  rw [priorType, priorHandle] at priorInput
  rw [convertTypeEq, convertHandle] at convertInput
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries context
      .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  exact .product factoryInput (.product wordInput (.product priorInput convertInput))

def SourceConstruction {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (callee factory prior convert source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ sources size, Dynamic.ValuesPack sources (packedSource factory prior convert) ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before callee sources (.value source) after

theorem collect {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (pack factory prior convert : Entry) (packMember : pack ∈ entries) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (packType : pack.sourceType = .function packedType (containerType fixture.dataType))
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {handle f p c : SourceCorePublicValues.Handle}
    (packHandle : pack.handle = handle) (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c)
    (call : ObservedConstruction publicSession handle f p c observed.readShape.instantiation)
    (invocation : Staging.Recursive.Scope) :
    ∃ (source : Dynamic.Value) (added : List Entry) (_collected : Collected observed source call.newOutput call.priorOutput call.factoryOutput call.builtinOutput added)
      (next : RetainedState support call.completion.session (entries ++ added)),
      SourceConstruction support invocation state.heap pack.source factory.source prior.source convert.source source next.heap := by
  have input := construction_input (context := support.makeHeader.header.function.context)
    factory prior convert factoryMember priorMember convertMember factoryType priorType convertTypeEq
    factoryHandle priorHandle convertHandle
  have returned : call.completion.value = outputValue observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput := by
    simpa only [observed.readShape.instantiationEq, outputValue, outputMetadata] using call.returned
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, started, _parameterView, _resultView,
    succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history pack packMember packType input state.atRecipe
      state.registry state.atSession (by simpa only [packHandle] using call.executed)
      (returned.symm ▸ outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput) invocation
  have originalSelected : RecursiveNamedPublicNestedOutputSelections.Selected fixture.recipe.compiled.compatible.checked actual.session
      (outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput)
      source payload nativeResult runOptions.outputValidationFuel added := selected_uncast returned.symm selected
  obtain ⟨collected⟩ := selected_entries observed originalSelected
  let next : RetainedState support call.completion.session (entries ++ added) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := by rw [contextAt]; exact returnedRegistry
    history := retained }
  exact ⟨source, added, collected, next, sources, sourceSize, packing, trace⟩

end Tests.SourceCoreConstructorCalls
