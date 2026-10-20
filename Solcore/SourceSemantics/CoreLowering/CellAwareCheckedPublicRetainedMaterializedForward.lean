import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
/-! Ordinary Source application reaches genuine public success from the
actual retained export, accepted packed request and current physical history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareCheckedPublicRetainedMaterializedForward
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
  (issued : SelectedCompilationCheckedRegistry.Certificate recipe.compiled)
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

local notation "cellModel" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (resultView : SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)

include profile receiver extension issued history inHistory entryType sourceEq retained input started parameterView metadata
  physical exactRegistry resultView ready atCheckpoint in
/-- Independent ordinary Source execution of a genuinely exported closure
supplies enough fuel for public success and preserves the complete prior history. -/
theorem source_success {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {value : Dynamic.Value} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources (.value value) after) :
    ∃ native finalStore finalMap finalWorld requiredExecution requiredOutput,
      ResultAt (registry := completion.result.context.registry) functions cellModel caller anchor.function.context result nativeResult
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
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cellModel)
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady := by
  exact CellAwareSelectedPublicRetainedMaterializedForward.source_success (invocation := invocation) functions profile receiver extension
    issued.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
    input started parameterView metadata physical exactRegistry resultView ready atCheckpoint packing arity trace

include profile receiver extension issued history inHistory entryType sourceEq retained input started parameterView metadata
  physical exactRegistry ready atCheckpoint in
/-- An independent ordinary Source fault reaches the public diagnostic and
keeps the exact failed heap and all earlier exported functions reusable. -/
theorem source_failure {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources (.fault reason) after) :
    ∃ native finalStore finalMap finalWorld requiredExecution token,
      ResultAt (registry := completion.result.context.registry) functions cellModel caller anchor.function.context result nativeResult
        (.fault (.semantic reason)) after native finalStore finalMap finalWorld callFaults ∧
      callFaults (.semantic reason) token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ CallableIndexedOwnedFunctionState.Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cellModel)
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt completion.result.context.registry ∧ returned.ExportsReady := by
  exact CellAwareSelectedPublicRetainedMaterializedForward.source_failure (invocation := invocation) functions profile receiver extension
    issued.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
    input started parameterView metadata physical exactRegistry ready atCheckpoint packing arity trace

include profile receiver extension issued history inHistory entryType sourceEq retained input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cellModel caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  exact CellAwareSelectedPublicRetainedMaterializedHandle.completed_reflects functions profile receiver extension
    issued.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
    input started parameterView metadata completed invocation

include profile receiver extension issued history inHistory entryType sourceEq retained input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome through the retained finite lexical body. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cellModel caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  exact CellAwareSelectedPublicRetainedMaterializedHandle.source_has_sufficient_fuel (invocation := invocation)
    functions profile receiver extension issued.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
    input started parameterView metadata packing arity trace

end Solcore.SourceSemantics.CoreLowering.CellAwareCheckedPublicRetainedMaterializedForward
