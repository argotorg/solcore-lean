import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFaultSource
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicResultContext
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues

/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureForward
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (callableProfile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
    prepared.named.specialized.function.inferredBodyType)
  {root : SourceCoreIndexedSession.Root whole}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial whole.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed)
    (program := Program.ofChecked whole.sourceProgram) headers root header)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨[], mapping, world, before, store,
    SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed⟩)
  (globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority whole mapping store)
  (stable : StableRows caller)
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (sidecarIssued : SourceCoreStageContracts.prepareSidecar whole.indexed.base.plan header.named.signature.key = .ok sidecar)
  (bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function
    (RecursiveStageRegistry.scope sidecar [] header.function))

local notation "rootFunctions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "rootCells" => GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile))
    mapping world header.bindings arguments payloads)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile))
      (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store)


variable {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {inputFuel : Nat}
  (sameCompiled : recipe.compiled = whole)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments inputFuel
    nativeCheckpoint recipe (sameCompiled.symm ▸ root) world store payloads encodedValues)


variable {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (exportsReady : nativeSession.ExportsReady)

def FailureForward (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required token,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        rootFunctions rootCells owner caller header capture payloads header.context
        (.fault failure) after value finalStore finalMap finalWorld faults ∧ faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact)
          (actual : SourceCoreIndexedSession.Session nativeArtifact)
          (reached : RecursiveNamedPublicFunctionHistory.Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          nativeCheckpoint.FailedResultAt executionFuel value finalStore token actual ∧
          returned.IndexedAt actual ∧ CallableIndexedOwnedFunctionState.Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
            (receiving := completion.result.context.registry) (anchor := header)
            actual finalMap finalWorld after finalStore reached [] ∧
          actual.RegistryAt completion.result.context.registry ∧ returned.ExportsReady

def ValueForward (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
    (∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld requiredExecution requiredOutput,
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.value source) after value finalStore finalMap finalWorld faults ∧
        ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
          requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
          publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
          ∃ (returned : SourceCoreExecution.Completion publicArtifact)
            (actual : SourceCoreIndexedSession.Completion nativeArtifact)
            (generation : SourceCorePublicValues.ExportGeneration)
            (reached : RecursiveNamedPublicFunctionHistory.Caller headers keys finalMap finalWorld after finalStore),
            outcome = .succeeded returned ∧
            nativeCheckpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
            returned.IndexedAt actual ∧ CallableIndexedOwnedFunctionState.Relates caller reached ∧
            CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
              (receiving := completion.result.context.registry) (anchor := header)
              actual.session finalMap finalWorld after finalStore reached [] ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller (.stage origin call reason) reached)

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_fault
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller (.stage origin call guard) reached := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel callableProfile receiver extension prepared aligned
      ready diagnostic wellFormed bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    (SelectedCompilationBodyTyping.Bodies.of_program wellFormed)).2
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, token, result, representedFault, output⟩
  | rejected origin call guard stagedContext reached =>
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inr ⟨origin, call, guard, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller source after := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel callableProfile receiver extension prepared aligned
      ready diagnostic wellFormed bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        (SelectedCompilationBodyTyping.Bodies.of_program wellFormed)).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
      (SelectedCompilationBodyTyping.Bodies.of_program wellFormed)).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureForward
