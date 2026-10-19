import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation

/-! The actual current public input and retained callee supply the deep heap
typing needed after a measured faulting materialized call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open CellAwarePublicApplicationResult (ResultAt)
open GeneralizedLocalMaterializedAssociation

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial recipe.compiled.compatible.checked).registry
    completion.result.context.registry)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (inHistory : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (sourceEq : entry.source = .closure function)
  (retained : CellAwareMaterializedRetainedEntries.EntryAt keys mapping world entry)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping wellFormed history inHistory entryType input started parameterView metadata in
theorem after_fault {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {size : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) stages size invocation
      anchor.function.context before entry.source sources (.fault failure) after) :
    Dynamic.HeapWellTyped anchor.function.context after := by
  have current := history.current
  have typed := (current.2.2.2.2 entry inHistory).2.2
  rw [entryType] at typed
  obtain ⟨_packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible
    started history input parameterView.symm metadata
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  exact (Staging.Recursive.FaultPreservation.applies wellFormed runtime
    current.2.2.2.1 typed packing packedTyped trace).1

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap
