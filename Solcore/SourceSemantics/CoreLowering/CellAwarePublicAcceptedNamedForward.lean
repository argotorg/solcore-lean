import Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedRoot
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicResultContext
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues

/-! A returning accepted body reaches actual public output from an independent
staged Source trace. The physical history of the returned session retains the
reached mixed heap, the physical cache authority and the exported function
values. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedForward
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwareInvocationAcceptedNamedHeaders (index)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (callableProfile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (support : SelectedCompilationNamedSupport.Support whole)
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
  (bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function
    (RecursiveStageRegistry.scope sidecar [] header.function))

variable
  (closed : CellAwareInvocationAcceptedExpressions.Closed (index prepared aligned))
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (body : AcceptedNamedBodyFlow.Body (index prepared aligned).policy (index prepared aligned).fuel
    (index prepared aligned).compilerSource (index prepared aligned).scope (index prepared aligned).statements
    (index prepared aligned).result (index prepared aligned).reasonAt (index prepared aligned).fellThrough
    (index prepared aligned).escaped (index prepared aligned).body)
  (covered : CellAwareInvocationAcceptedFlow.Covered (index prepared aligned).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (index prepared aligned))
    (CellAwareInvocationAcceptedInputs.Generalized (index prepared aligned)) body.tree)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
      (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile))
    mapping world header.bindings arguments payloads)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile))
      (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store)
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {inputFuel : Nat}
  (sameCompiled : recipe.compiled = whole)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments inputFuel
    nativeCheckpoint recipe (sameCompiled.symm ▸ root) world store payloads encodedValues)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (exportsReady : nativeSession.ExportsReady)

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions)
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected closed artifact checked covered represented heaps
  sameCompiled started atCheckpoint exactRegistry exportsReady in
/-- A staged Source trace that returns a value determines the actual public
resumption: it succeeds with the exported value, and the returned session has a
physical history in the accepted cell model. -/
theorem first_value_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext (.returned source) after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld requiredExecution requiredOutput,
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions accepted owner caller header capture payloads header.context
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
            CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := accepted)
              (receiving := completion.result.context.registry) (anchor := header)
              actual.session finalMap finalWorld after finalStore reached [] ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected callableProfile receiver prepared aligned
      ready diagnostic support selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      bodySelected closed artifact checked body covered represented heaps rfl started allocated trace
  have publicResult := result.context
    (SelectedCompilationPublicReturnedValues.header_context_supports header header support.bodyTyping).2
  obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
    exactRegistry exportsReady atCheckpoint publicResult run physical
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedForward
