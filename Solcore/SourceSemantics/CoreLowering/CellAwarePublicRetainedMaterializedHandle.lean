import Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler

/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
The row is recovered from the positively retained output certificate. No
caller supplies an association or a call meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
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
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping history inHistory entryType sourceEq in
/-- Current retained typing identifies the actual Source frame before the
independent call trace is constructed. No completed target call is needed. -/
theorem source_frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function := by
  obtain ⟨_imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  rw [entryType, sourceEq] at typed
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := typed.closure_function_inv
  exact ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
    sourceCode.requirement_ledger.idsUnique, evidence⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
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
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.completed_reflects functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata completed invocation

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
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
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.has_sufficient_fuel functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
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
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.source_has_sufficient_fuel (invocation := invocation) functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
