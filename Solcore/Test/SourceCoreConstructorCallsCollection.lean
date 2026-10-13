import Solcore.Test.SourceCoreConstructorCallsIssuance
import Solcore.Test.SourceCoreConstructorCallsSelectionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectOutputCollection
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
  obtain ⟨sources, packing, _arity, source, added, next, sourceSize, trace, _handles, selected⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectOutputCollection.State.collect support.program
      fixture.recipePrepared state pack packMember packType input
      (by simpa only [packHandle] using call.executed)
      (returned.symm ▸ outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput)
      invocation
  obtain ⟨_artifact, _actual, _native, _type, _atCompletion, selected⟩ := selected
  obtain ⟨collected⟩ := selected_entries observed (selected_uncast returned.symm selected)
  exact ⟨source, added, collected, next, sources, sourceSize, packing, trace⟩

end Tests.SourceCoreConstructorCalls
