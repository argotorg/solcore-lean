import Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinPackedApplication
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin

/-! Actual history and input encoding supply direct callable arguments.
The retained builtin keeps its genuine compiler identity. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleForward
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open CellAwarePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {bodyFaults : FunctionCalls.FaultRep}
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  (cells : GenericHeap.CellModel recipe.compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile) cells
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : BuiltinFunctionId} (sourceEq : entry.source = .builtin ⟨function⟩)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functionModel" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (resultView : SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)

include profile cells history member entryType sourceEq input started parameterView metadata
  physical exactRegistry resultView ready atCheckpoint in
/-- Independent ordinary Source execution of a genuinely exported builtin
supplies enough fuel for public success and preserves the complete prior history. -/
theorem source_success {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {value : Dynamic.Value} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources (.value value) after) :
    ∃ native finalStore finalMap finalWorld requiredExecution requiredOutput,
      ResultAt (registry := completion.result.context.registry) functionModel cells caller anchor.function.context result nativeResult
        (.value value) after native finalStore finalMap finalWorld callFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded returned ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          returned.IndexedAt actual ∧ CallableIndexedOwnedFunctionState.Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functionModel) (cells := cells)
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady := by
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwarePublicBuiltinHandleMeaning.source_has_sufficient_fuel (invocation := invocation)
      profile cells history entry member entryType sourceEq
      input started parameterView metadata packing trace
  obtain ⟨requiredOutput, exported⟩ := CellAwarePublicDirectOutput.after_success functionModel cells started
    exactRegistry resultView ready atCheckpoint semantic runs ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, semantic, exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleForward
