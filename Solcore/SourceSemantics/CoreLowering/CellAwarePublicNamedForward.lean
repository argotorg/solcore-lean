import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedSource
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicResultContext
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues

/-! Ordinary Source success reaches actual public output with reusable mixed
history, or a real earlier stage rejection with its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
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
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults)

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
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults) := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile receiver extension prepared aligned
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
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
