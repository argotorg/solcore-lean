import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler

/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
Only compiler provenance identifies the row; no call meaning is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
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
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}
  (association : Association recipe.compiled mapping world function entry.native bindings parameterCore resultCore)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (atFrame : association.AtFrame owner.key.frameLocation)
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
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include history inHistory entryType sourceEq input started parameterView metadata in
private theorem current_inputs :
    callable = entry.native ∧
    Dynamic.ValueHasType anchor.function.context before (.closure function) (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  have callableEq := started.callable_eq imported
  rw [entryType, sourceEq] at typed
  obtain ⟨packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible started history input parameterView.symm metadata
  exact ⟨callableEq, typed, packedRelated, packedTyped⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  rw [callableEq] at measured
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.reflects functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) wellFormed heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps measured
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld,
    by simpa only [sourceEq] using trace, resultAt⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- A finite independent Source call supplies sufficient fuel for the same
accepted public checkpoint, including its exact failure store. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
      anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  rw [sourceEq] at trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.preserves functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) wellFormed heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  rw [← callableEq] at evaluated
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome because this retained body is a terminal read. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨_callableEq, calleeTyped, _packedRelated, _packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  have runtime := anchor_runtime (anchor := anchor) bodyTyping
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
      sourceCode.requirement_ledger.idsUnique, evidence⟩
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (Staging.Recursive.Lifting.embed outcome) after := by
    rw [sourceEq] at trace ⊢
    exact GeneralizedLocalSourceApplicationLifting.selected_association_exact association frame arity.symm trace
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  exact has_sufficient_fuel functions profile receiver extension bodyTyping wellFormed history entry inHistory
    entryType sourceEq association owner atFrame input started parameterView metadata packing arity measured

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
