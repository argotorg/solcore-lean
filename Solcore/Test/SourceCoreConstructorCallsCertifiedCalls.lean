import Solcore.Test.SourceCoreConstructorCallsCertifiedMeaning
import Solcore.Test.SourceCoreConstructorCallsCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectWordForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectOutputForward

/-! The complete automatic catalog follows the original packed constructor
call, its ordered selected handles, and every subsequent retained invocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open CertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure ConstructionMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (pack factory prior convert : Entry)
    {handle f p c : SourceCorePublicValues.Handle}
    (call : ObservedConstruction session handle f p c observed.readShape.instantiation)
    (scope : Staging.Recursive.Scope) where
  member : pack ∈ entries
  packType : pack.sourceType = .function packedType (containerType fixture.dataType)
  handleEq : pack.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context packedType
    (packedArgument f p c) (packedSource factory.source prior.source convert.source)
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments (packedSource factory.source prior.source convert.source)
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    pack.source arguments.length
  source : Dynamic.Value
  added : List Entry
  collected : Collected observed source call.newOutput call.priorOutput call.factoryOutput call.builtinOutput added
  after : issued.State anchor call.completion.session (entries ++ added)
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap pack.source arguments (.value source) after.heap

theorem construction_meaning (before : issued.State anchor session entries)
    (pack factory prior convert : Entry) (packMember : pack ∈ entries) (factoryMember : factory ∈ entries)
    (priorMember : prior ∈ entries) (convertMember : convert ∈ entries)
    (packType : pack.sourceType = .function packedType (containerType fixture.dataType))
    (factoryType : factory.sourceType = makerType) (priorType : prior.sourceType = closureType)
    (convertTypeEq : convert.sourceType = convertType)
    {handle f p c : SourceCorePublicValues.Handle}
    (packHandle : pack.handle = handle) (factoryHandle : factory.handle = f)
    (priorHandle : prior.handle = p) (convertHandle : convert.handle = c)
    (call : ObservedConstruction session handle f p c observed.readShape.instantiation)
    (scope : Staging.Recursive.Scope) :
    Nonempty (ConstructionMeaning issued before pack factory prior convert call scope) := by
  have input := construction_input (context := anchor.function.context)
    factory prior convert factoryMember priorMember convertMember factoryType priorType convertTypeEq
    factoryHandle priorHandle convertHandle
  have returned : call.completion.value = outputValue observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput := by
    simpa only [observed.readShape.instantiationEq, outputValue, outputMetadata] using call.returned
  obtain ⟨arguments, packing, arity, source, added, after, size, trace, _handles, selected⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectOutputCollection.State.collect issued.support issued.prepared
      before pack packMember packType input (by simpa only [packHandle] using call.executed)
      (returned.symm ▸ outputSelection observed call.newOutput call.priorOutput call.factoryOutput call.builtinOutput) scope
  obtain ⟨_artifact, _actual, _native, _type, _atCompletion, selected⟩ := selected
  obtain ⟨collected⟩ := selected_entries observed (selected_uncast returned.symm selected)
  exact ⟨⟨packMember, packType, packHandle, input, arguments, packing, arity,
    source, added, collected, after, size, trace⟩⟩

structure WordMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (parameter : TypeSystem.Ty)
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    (packed : Dynamic.Value) (call : ObservedInvocation session handle argument)
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter .word
  handleEq : entry.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments packed
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem word_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packed : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed)
    (call : ObservedInvocation session handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (WordMeaning issued before entry parameter packed call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType) input
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, input, arguments, packing, arity, after, size, trace⟩⟩

structure SuccessMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (parameter result : TypeSystem.Ty)
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    (packed : Dynamic.Value) (call : ObservedInvocation session handle argument)
    (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter result
  handleEq : entry.handle = handle
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments packed
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  source : Dynamic.Value
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value source) after.heap

theorem success_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packed : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packed)
    (call : ObservedInvocation session handle argument) (scope : Staging.Recursive.Scope) :
    Nonempty (SuccessMeaning issued before entry parameter result packed call scope) := by
  obtain ⟨arguments, packing, arity, source, after, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectSuccessStep.State.invoke_success issued.support issued.prepared
      before entry member entryType input (by simpa only [handleEq] using call.executed) scope
  exact ⟨⟨member, entryType, handleEq, input, arguments, packing, arity, source, after, size, trace⟩⟩

theorem ConstructionMeaning.forward
    {before : issued.State anchor session entries} {pack factory prior convert : Entry}
    {handle f p c : SourceCorePublicValues.Handle}
    {call : ObservedConstruction session handle f p c observed.readShape.instantiation}
    {scope : Staging.Recursive.Scope}
    (meaning : ConstructionMeaning issued before pack factory prior convert call scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle (packedArgument f p c) runOptions.inputValidationFuel = .ok checkpoint ∧
      RecursiveNamedPublicPhysicalSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (containerType fixture.dataType)
        checkpoint meaning.source meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectOutputForward.forward_call issued.support issued.prepared
    before pack meaning.member meaning.packType meaning.input
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

theorem WordMeaning.forward {before : issued.State anchor session entries} {entry : Entry}
    {parameter : TypeSystem.Ty} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {packed : Dynamic.Value} {call : ObservedInvocation session handle argument}
    {word : Core.Word} {scope : Staging.Recursive.Scope}
    (meaning : WordMeaning issued before entry parameter packed call word scope) :
    ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
      RecursiveNamedPublicPhysicalSessionDirectWordForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries word checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectWordForward.forward_call issued.support issued.prepared
    before entry meaning.member word meaning.entryType meaning.input
    (by simpa only [meaning.handleEq] using accepted) meaning.packing meaning.trace

theorem SuccessMeaning.forward {before : issued.State anchor session entries} {entry : Entry}
    {parameter result : TypeSystem.Ty} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {packed : Dynamic.Value} {call : ObservedInvocation session handle argument} {scope : Staging.Recursive.Scope}
    (meaning : SuccessMeaning issued before entry parameter result packed call scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
      RecursiveNamedPublicPhysicalSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries result checkpoint meaning.source meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectOutputForward.forward_call issued.support issued.prepared
    before entry meaning.member meaning.entryType meaning.input
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreConstructorCalls.CompilerProfile
