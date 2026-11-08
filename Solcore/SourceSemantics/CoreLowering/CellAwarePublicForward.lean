import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHandles
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.Staging.Internal.FaultCalls
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.MaterializedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.PublicSessions

/-!
# Cell-aware public outcomes

From an independent Source trace to actual public output, for the first call and for
later calls, for each family of cell-aware bodies; and back from a public completion to
Source. The results keep the reached physical history, so later calls can chain.

Main declarations:
- `CellAwarePublicNamedForward.first_value` and
  `CellAwarePublicNamedContinuation.after_value`, values at the first and later calls;
- `CellAwarePublicNamedFailureForward.first_fault` and
  `CellAwarePublicNamedFailureContinuation.after_fault`, faults at the same two places;
- `CellAwarePublicNamedFailureReflection.Reflected`, what a public completion reflects to;
- `CellAwarePublicLexicalForward.first_value`, `CellAwarePublicImperativeNamedForward.first_value`
  and `CellAwarePublicFaultingFailureForward.first_value`, the other families;
- `CellAwarePublicRetainedMaterializedForward.source_success`,
  `CellAwareCheckedPublicRetainedMaterializedForward.source_success` and
  `CellAwareProfiledPublicRetainedMaterializedForward.source_success`, calls through a
  retained function handle.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        (support.bodyTyping)).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
/-! Ordinary Source success reaches actual public output with reusable mixed
history, or a real earlier stage rejection with its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
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
  (support : SelectedCompilationNamedSupport.Support whole)
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

def ValueForward (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults)

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value_selected
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := header)
      nativeSession mapping world before store caller entries)
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
              actual.session finalMap finalWorld after finalStore reached entries ∧
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
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        (support.bodyTyping)).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.after_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := header)
      nativeSession mapping world before store caller entries)
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
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults) := by
  apply after_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_fault_selected
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
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureContinuation
/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureContinuation
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
  (support : SelectedCompilationNamedSupport.Support whole)
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

def FailureForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
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
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt completion.result.context.registry ∧ returned.ExportsReady

def ValueForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
              (receiving := completion.result.context.registry) (anchor := anchor)
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call reason) reached)

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, token, result, representedFault, output⟩
  | rejected origin call guard stagedContext reached =>
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, guard, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicNamedFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.after_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  apply after_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  apply after_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureReflection
/-! An actual public failed event reflects through the accepted mixed body.
Semantic failures recover the original Source fault and exact reached heap;
stage failures retain their actual staged origin. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureReflection
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
  (support : SelectedCompilationNamedSupport.Support whole)
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

structure Reflected (executionFuel : Nat) (token : Word)
    (returned : SourceCoreExecution.Session publicArtifact) where
  actual : SourceCoreIndexedSession.Session nativeArtifact
  capture : NamedCapture headers owner.key header mapping world
  value : Value
  finalStore : Store
  size : Nat
  environment : Dynamic.Environment
  bound : Dynamic.Heap
  finalContext : SourceSemantics.Context
  failure : Staging.Recursive.Failure
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  failed : nativeCheckpoint.FailedResultAt executionFuel value finalStore token actual
  atSession : returned.IndexedAt actual
  allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound
  trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
    (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
    header.function.body finalContext (.fault failure) after
  plain : ∀ reason, failure = .semantic reason →
    Dynamic.FunctionStatementsFault (Program.ofChecked whole.sourceProgram) header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext reason after
  result : CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
    rootFunctions rootCells owner caller header capture payloads header.context
    (.fault failure) after value finalStore finalMap finalWorld faults
  fault : faults failure token
  heap : Dynamic.HeapWellTyped header.context after
  registry : actual.RegistryAt completion.result.context.registry
  exports : returned.ExportsReady

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect_selected {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  cases sameCompiled
  obtain ⟨actual, _generation, value, finalStore, completed, failed, atSession⟩ := resumed.indexed_failed atCheckpoint
  obtain ⟨capture, size, environment, bound, finalContext, outcome, after, finalMap, finalWorld,
      allocated, trace, matched, result⟩ :=
    CellAwarePublicNamedRoot.checkpoint_reflects_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps rfl started completed
  obtain ⟨failure, outcomeEq⟩ : ∃ failure,
      CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = .fault failure := by
    have represented := result.2.1
    generalize rawEq : CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = rawOutcome at represented ⊢
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  have receipt := SelectedCompilationNamedAdmission.parameter_source (support.certified header) allocated heapTyped argumentsTyped
  obtain ⟨staticFinal, facts, typed, _complete⟩ := receipt.bodyTyped
  have sourceEq := (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled).source bodySelected
  have bodyTyped : StatementsHaveType (RecursiveStageRegistry.scope sidecar [] header.function).source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [sourceEq] using typed
  have unique : NodeOccurrencesUnique (RecursiveStageRegistry.scope sidecar [] header.function).source := by
    simpa only [sourceEq] using header.unique
  have closed := Staging.Recursive.TypedControlBoundary.function unique bodyTyped rfl trace.sound
  have bodyEq := Staging.Recursive.TypedControlBoundary.body_fault closed (outcomeEq ▸ matched)
  have traceFault := bodyEq ▸ trace
  have resultFault := outcomeEq ▸ result
  have related : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics failure token := by
    have represented := resultFault.2.1
    cases represented with
    | fault related =>
      have decoded := failed.2.1
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
      exact decoded ▸ related
  have registryAt : actual.RegistryAt completion.result.context.registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  refine ⟨{
    actual := actual, capture := capture, value := value, finalStore := finalStore,
    size := size, environment := environment, bound := bound, finalContext := finalContext,
    failure := failure, after := after, finalMap := finalMap, finalWorld := finalWorld,
    failed := failed, atSession := atSession, allocated := allocated, trace := traceFault, plain := ?_,
    result := resultFault, fault := related, heap := ?_, registry := registryAt, exports := ?_ }⟩
  · intro reason same
    subst failure
    exact traceFault.sound.semanticFault_plain
  · exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated traceFault
  · exact atSession.exportsReady_iff.mpr (failed.exportsReady (started.original.initial_registry.exportsReady exportsReady))

variable {executionFuel : Nat} {token : Word} {returned : SourceCoreExecution.Session publicArtifact}
  (observed : Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
    (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
    (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned)

include selected support started sameCompiled physical in
theorem Reflected.first_history_selected :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := CellAwarePublicFunctionHistory.first_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, retained, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩

include selected support started sameCompiled in
theorem Reflected.after_history_selected {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := history.semantic.after_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, history.after_result result retained⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  apply reflect_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include selected wellFormed started sameCompiled physical in
theorem Reflected.first_history :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  apply Reflected.first_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) (physical := physical) <;> assumption

include selected wellFormed started sameCompiled in
theorem Reflected.after_history {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  apply Reflected.after_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailureReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalForward
/-! Ordinary Source success reaches actual public output with reusable mixed
history, or a real earlier stage rejection with its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareLexicalNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld,
      required, adapted, run, result⟩ :=
    CellAwarePublicLexicalSourceRoot.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureForward
/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareLexicalNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_fault_selected
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
    CellAwarePublicLexicalFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
    CellAwarePublicLexicalFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureContinuation
/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureContinuation
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareLexicalNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

def FailureForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
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
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt completion.result.context.registry ∧ returned.ExportsReady

def ValueForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
              (receiving := completion.result.context.registry) (anchor := anchor)
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call reason) reached)

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicLexicalFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, token, result, representedFault, output⟩
  | rejected origin call guard stagedContext reached =>
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, guard, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicLexicalFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.after_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  apply after_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  apply after_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureReflection
/-! An actual public failed event reflects through the accepted mixed body.
Semantic failures recover the original Source fault and exact reached heap;
stage failures retain their actual staged origin. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureReflection
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareLexicalNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

structure Reflected (executionFuel : Nat) (token : Word)
    (returned : SourceCoreExecution.Session publicArtifact) where
  actual : SourceCoreIndexedSession.Session nativeArtifact
  capture : NamedCapture headers owner.key header mapping world
  value : Value
  finalStore : Store
  size : Nat
  environment : Dynamic.Environment
  bound : Dynamic.Heap
  finalContext : SourceSemantics.Context
  failure : Staging.Recursive.Failure
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  failed : nativeCheckpoint.FailedResultAt executionFuel value finalStore token actual
  atSession : returned.IndexedAt actual
  allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound
  trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
    (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
    header.function.body finalContext (.fault failure) after
  plain : ∀ reason, failure = .semantic reason →
    Dynamic.FunctionStatementsFault (Program.ofChecked whole.sourceProgram) header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext reason after
  result : CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
    rootFunctions rootCells owner caller header capture payloads header.context
    (.fault failure) after value finalStore finalMap finalWorld faults
  fault : faults failure token
  heap : Dynamic.HeapWellTyped header.context after
  registry : actual.RegistryAt completion.result.context.registry
  exports : returned.ExportsReady

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect_selected {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  cases sameCompiled
  obtain ⟨actual, _generation, value, finalStore, completed, failed, atSession⟩ := resumed.indexed_failed atCheckpoint
  obtain ⟨capture, size, environment, bound, finalContext, outcome, after, finalMap, finalWorld,
      allocated, trace, matched, result⟩ :=
    CellAwarePublicLexicalNamedRoot.checkpoint_reflects_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps rfl started completed
  obtain ⟨failure, outcomeEq⟩ : ∃ failure,
      CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = .fault failure := by
    have represented := result.2.1
    generalize rawEq : CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = rawOutcome at represented ⊢
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  have receipt := SelectedCompilationNamedAdmission.parameter_source (support.certified header) allocated heapTyped argumentsTyped
  obtain ⟨staticFinal, facts, typed, _complete⟩ := receipt.bodyTyped
  have sourceEq := (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled).source bodySelected
  have bodyTyped : StatementsHaveType (RecursiveStageRegistry.scope sidecar [] header.function).source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [sourceEq] using typed
  have unique : NodeOccurrencesUnique (RecursiveStageRegistry.scope sidecar [] header.function).source := by
    simpa only [sourceEq] using header.unique
  have closed := Staging.Recursive.TypedControlBoundary.function unique bodyTyped rfl trace.sound
  have bodyEq := Staging.Recursive.TypedControlBoundary.body_fault closed (outcomeEq ▸ matched)
  have traceFault := bodyEq ▸ trace
  have resultFault := outcomeEq ▸ result
  have related : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics failure token := by
    have represented := resultFault.2.1
    cases represented with
    | fault related =>
      have decoded := failed.2.1
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
      exact decoded ▸ related
  have registryAt : actual.RegistryAt completion.result.context.registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  refine ⟨{
    actual := actual, capture := capture, value := value, finalStore := finalStore,
    size := size, environment := environment, bound := bound, finalContext := finalContext,
    failure := failure, after := after, finalMap := finalMap, finalWorld := finalWorld,
    failed := failed, atSession := atSession, allocated := allocated, trace := traceFault, plain := ?_,
    result := resultFault, fault := related, heap := ?_, registry := registryAt, exports := ?_ }⟩
  · intro reason same
    subst failure
    exact traceFault.sound.semanticFault_plain
  · exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated traceFault
  · exact atSession.exportsReady_iff.mpr (failed.exportsReady (started.original.initial_registry.exportsReady exportsReady))

variable {executionFuel : Nat} {token : Word} {returned : SourceCoreExecution.Session publicArtifact}
  (observed : Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
    (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
    (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned)

include selected support started sameCompiled physical in
theorem Reflected.first_history_selected :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := CellAwarePublicFunctionHistory.first_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, retained, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩

include selected support started sameCompiled in
theorem Reflected.after_history_selected {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := history.semantic.after_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, history.after_result result retained⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  apply reflect_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include selected wellFormed started sameCompiled physical in
theorem Reflected.first_history :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  apply Reflected.first_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) (physical := physical) <;> assumption

include selected wellFormed started sameCompiled in
theorem Reflected.after_history {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  apply Reflected.after_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFailureReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureForward
/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareFaultingNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_fault_selected
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
    CellAwarePublicFaultingFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
    CellAwarePublicFaultingFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.first_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run physical
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureContinuation
/-! Independent Source faults and actual earlier stage stops reach the public
failed session with their exact heap and reusable physical function history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureContinuation
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareFaultingNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

def FailureForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
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
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt completion.result.context.registry ∧ returned.ExportsReady

def ValueForward (anchor : Header whole (Program.ofChecked whole.sourceProgram))
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
              (receiving := completion.result.context.registry) (anchor := anchor)
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call reason) reached)

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicFaultingFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, token, result, representedFault, output⟩
  | rejected origin call guard stagedContext reached =>
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, guard, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value_selected
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    CellAwarePublicFaultingFaultSource.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
        support.bodyTyping).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.after_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
      support.bodyTyping).2
    have publicResult := result.context supports
    obtain ⟨token, representedFault, output⟩ := CellAwarePublicNamedFailure.after_failure _ _ selected started
      exactRegistry exportsReady atCheckpoint ((faultHeap _ rfl).transportContext supports) publicResult run history
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld,
      required, token, result, representedFault, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_fault
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.fault reason) after) :
    FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.semantic reason) after ∨
      ∃ origin call guard reached, FailureForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries (.stage origin call guard) reached := by
  apply after_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value
    {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {source : Dynamic.Value}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext (.returned source) after) :
    ValueForward (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads)
      (nativeCheckpoint := nativeCheckpoint) (publicCheckpoint := publicCheckpoint) callableProfile owner caller anchor entries source after := by
  apply after_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureReflection
/-! An actual public failed event reflects through the accepted mixed body.
Semantic failures recover the original Source fault and exact reached heap;
stage failures retain their actual staged origin. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureReflection
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareFaultingNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

structure Reflected (executionFuel : Nat) (token : Word)
    (returned : SourceCoreExecution.Session publicArtifact) where
  actual : SourceCoreIndexedSession.Session nativeArtifact
  capture : NamedCapture headers owner.key header mapping world
  value : Value
  finalStore : Store
  size : Nat
  environment : Dynamic.Environment
  bound : Dynamic.Heap
  finalContext : SourceSemantics.Context
  failure : Staging.Recursive.Failure
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  failed : nativeCheckpoint.FailedResultAt executionFuel value finalStore token actual
  atSession : returned.IndexedAt actual
  allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound
  trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
    (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
    header.function.body finalContext (.fault failure) after
  plain : ∀ reason, failure = .semantic reason →
    Dynamic.FunctionStatementsFault (Program.ofChecked whole.sourceProgram) header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext reason after
  result : CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
    rootFunctions rootCells owner caller header capture payloads header.context
    (.fault failure) after value finalStore finalMap finalWorld faults
  fault : faults failure token
  heap : Dynamic.HeapWellTyped header.context after
  registry : actual.RegistryAt completion.result.context.registry
  exports : returned.ExportsReady

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect_selected {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  cases sameCompiled
  obtain ⟨actual, _generation, value, finalStore, completed, failed, atSession⟩ := resumed.indexed_failed atCheckpoint
  obtain ⟨capture, size, environment, bound, finalContext, outcome, after, finalMap, finalWorld,
      allocated, trace, matched, result⟩ :=
    CellAwarePublicFaultingNamedRoot.checkpoint_reflects_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps rfl started completed
  obtain ⟨failure, outcomeEq⟩ : ∃ failure,
      CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = .fault failure := by
    have represented := result.2.1
    generalize rawEq : CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome = rawOutcome at represented ⊢
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  have receipt := SelectedCompilationNamedAdmission.parameter_source (support.certified header) allocated heapTyped argumentsTyped
  obtain ⟨staticFinal, facts, typed, _complete⟩ := receipt.bodyTyped
  have sourceEq := (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled).source bodySelected
  have bodyTyped : StatementsHaveType (RecursiveStageRegistry.scope sidecar [] header.function).source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [sourceEq] using typed
  have unique : NodeOccurrencesUnique (RecursiveStageRegistry.scope sidecar [] header.function).source := by
    simpa only [sourceEq] using header.unique
  have closed := Staging.Recursive.TypedControlBoundary.function unique bodyTyped rfl trace.sound
  have bodyEq := Staging.Recursive.TypedControlBoundary.body_fault closed (outcomeEq ▸ matched)
  have traceFault := bodyEq ▸ trace
  have resultFault := outcomeEq ▸ result
  have related : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics failure token := by
    have represented := resultFault.2.1
    cases represented with
    | fault related =>
      have decoded := failed.2.1
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
      exact decoded ▸ related
  have registryAt : actual.RegistryAt completion.result.context.registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  refine ⟨{
    actual := actual, capture := capture, value := value, finalStore := finalStore,
    size := size, environment := environment, bound := bound, finalContext := finalContext,
    failure := failure, after := after, finalMap := finalMap, finalWorld := finalWorld,
    failed := failed, atSession := atSession, allocated := allocated, trace := traceFault, plain := ?_,
    result := resultFault, fault := related, heap := ?_, registry := registryAt, exports := ?_ }⟩
  · intro reason same
    subst failure
    exact traceFault.sound.semanticFault_plain
  · exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated traceFault
  · exact atSession.exportsReady_iff.mpr (failed.exportsReady (started.original.initial_registry.exportsReady exportsReady))

variable {executionFuel : Nat} {token : Word} {returned : SourceCoreExecution.Session publicArtifact}
  (observed : Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
    (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
    (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned)

include selected support started sameCompiled physical in
theorem Reflected.first_history_selected :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header header
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := CellAwarePublicFunctionHistory.first_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, retained, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩

include selected support started sameCompiled in
theorem Reflected.after_history_selected {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  cases sameCompiled
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor
    support.bodyTyping).2
  have result := observed.result.context supports
  obtain ⟨reached, related, retained⟩ := history.semantic.after_failure
    rfl started selected observed.failed result (observed.heap.transportContext supports)
  exact ⟨reached, related, history.after_result result retained⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem reflect {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    Nonempty (Reflected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (completion := completion) (header := header) (payloads := payloads) (arguments := arguments)
      (nativeCheckpoint := nativeCheckpoint) (sidecar := sidecar) callableProfile owner caller executionFuel token returned) := by
  apply reflect_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

include selected wellFormed started sameCompiled physical in
theorem Reflected.first_history :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached [] := by
  apply Reflected.first_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) (physical := physical) <;> assumption

include selected wellFormed started sameCompiled in
theorem Reflected.after_history {anchor : Header whole (Program.ofChecked whole.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := anchor)
      nativeSession mapping world before store caller entries) :
    ∃ reached : CellAwarePublicFunctionHistory.Caller headers keys observed.finalMap observed.finalWorld
      observed.after observed.finalStore,
      Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := rootCells)
        (receiving := completion.result.context.registry) (anchor := anchor)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached entries := by
  apply Reflected.after_history_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (started := started) (sameCompiled := sameCompiled) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedForward
/-! The common imperative body reaches actual public output from an independent
Source trace. Its existing output receipt preserves the reached mixed history
for subsequent calls and records a genuine earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedForward
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem first_value_selected
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
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld,
      required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        (support.bodyTyping)).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.first_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run physical
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply first_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedContinuation
/-! The common imperative body reaches actual public output from an independent
Source trace. Its existing output receipt preserves the reached mixed history
for subsequent calls and records a genuine earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedContinuation
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
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value_selected
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := header)
      nativeSession mapping world before store caller entries)
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
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults) := by
  cases sameCompiled
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld,
      required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel_selected callableProfile receiver extension prepared aligned
      ready diagnostic support bodyProfile selected owner caller globalReference keyPhysical physical stable
      heapTyped argumentsTyped sidecarIssued bodySelected represented heaps rfl started allocated trace
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports header header
        (support.bodyTyping)).2
    obtain ⟨requiredOutput, output⟩ := CellAwarePublicNamedOutput.after_success _ _ selected started
      exactRegistry exportsReady atCheckpoint publicResult run history
    exact .inl ⟨capture, value, finalStore, finalMap, finalWorld, required, requiredOutput, result, output⟩
  | rejected origin call reason stagedContext reached =>
    exact .inr ⟨origin, call, reason, reached, capture, value, finalStore, finalMap, finalWorld, required, run, result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started
  atCheckpoint exactRegistry exportsReady in
theorem after_value
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (history : CellAwarePublicPhysicalHistory.History
      (functions := rootFunctions) (cells := rootCells)
      (receiving := completion.result.context.registry) (anchor := header)
      nativeSession mapping world before store caller entries)
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
              actual.session finalMap finalWorld after finalStore reached entries ∧
            actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady) ∨
    (∃ origin call reason reached,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
        CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
          rootFunctions rootCells owner caller header capture payloads header.context
          (.fault (.stage origin call reason)) reached value finalStore finalMap finalWorld faults) := by
  apply after_value_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) (atCheckpoint := atCheckpoint) (exactRegistry := exactRegistry) (exportsReady := exportsReady) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedForward
/-! Ordinary Source application reaches genuine public success from the
actual retained export, accepted packed request and current physical history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedForward
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

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata
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
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwarePublicRetainedMaterializedHandle.source_has_sufficient_fuel (invocation := invocation)
      functions profile receiver extension bodyTyping wellFormed history entry inHistory entryType sourceEq retained
      input started parameterView metadata packing arity trace
  obtain ⟨requiredOutput, exported⟩ := CellAwarePublicDirectOutput.after_success functions cellModel started
    exactRegistry resultView ready atCheckpoint semantic runs ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, semantic, exported⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata
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
  obtain ⟨owner, bindings, parameterCore, resultCore, association, _framed⟩ := retained.association sourceEq
  have frame := CellAwarePublicRetainedMaterializedHandle.source_frame functions bodyTyping history
    entry inHistory entryType sourceEq
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (.fault (.semantic reason)) after := by
    rw [sourceEq] at trace ⊢
    exact GeneralizedLocalSourceApplicationLifting.selected_association_exact association frame (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)
      (CellAwarePublicMaterializedHandleMeaning.source_arguments functions bodyTyping history entry inHistory
        entryType sourceEq input started parameterView metadata packing arity) arity.symm trace
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  have heapTyped := CellAwarePublicMaterializedFaultHeap.after_fault functions bodyTyping wellFormed history
    entry inHistory entryType input started parameterView metadata packing measured
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwarePublicRetainedMaterializedHandle.source_has_sufficient_fuel (invocation := invocation)
      functions profile receiver extension bodyTyping wellFormed history entry inHistory entryType sourceEq retained
      input started parameterView metadata packing arity trace
  obtain ⟨token, fault, failed⟩ := CellAwarePublicDirectFailure.after_failure functions cellModel started
    exactRegistry ready atCheckpoint semantic runs heapTyped ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, token, semantic, fault, failed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedReflection
/-! Observed public handle completion reconstructs independent Source meaning
from its authentic retained materialized row and actual current public inputs.
Both success and failure retain the exact reached physical state and history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedReflection
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
  (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells :=
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    ) (receiving := completion.result.context.registry) (anchor := anchor)
    session mapping world before store caller entries)
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

local notation "rootCells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (exportsReady : session.ExportsReady)

structure Succeeded (executionFuel outputFuel : Nat)
    (publicCompletion : SourceCoreExecution.Completion publicArtifact) (invocation : Staging.Recursive.Scope) where
  actual : Completion artifact
  generation : SourceCorePublicValues.ExportGeneration
  native : Core.Value
  finalStore : Store
  sources : List Dynamic.Value
  packing : Dynamic.ValuesPack sources packedSource
  arity : sources.length = function.parameters.length
  size : Nat
  source : Dynamic.Value
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  reached : Caller headers keys finalMap finalWorld after finalStore
  completed : checkpoint.NativeDone executionFuel native finalStore
  exported : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual
  atCompletion : publicCompletion.IndexedAt actual
  trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages size invocation
    anchor.function.context before entry.source sources (.value source) after
  plain : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
    invocation.evidence (Staging.Recursive.callableEvidence entry.source) before entry.source sources source after
  result : ResultAt (registry := completion.result.context.registry) functions rootCells caller anchor.function.context result nativeResult
    (.value source) after native finalStore finalMap finalWorld callFaults
  related : CallableIndexedOwnedFunctionState.Relates caller reached
  history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := rootCells)
    (receiving := completion.result.context.registry) (anchor := anchor)
    actual.session finalMap finalWorld after finalStore reached entries
  registry : actual.session.RegistryAt completion.result.context.registry
  exports : actual.session.ExportsReady

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started
  parameterView metadata atCheckpoint exactRegistry exportsReady in
/-- A successful public resume recovers the exact ordinary Source call, without
a Source execution or closure association supplied by the caller. -/
theorem succeeded {executionFuel outputFuel : Nat}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    Nonempty (Succeeded (completion := completion) (caller := caller) (anchor := anchor) (result := result) (function := function) (packedSource := packedSource)
      (entry := entry) (entries := entries) (nativeResult := nativeResult) (checkpoint := checkpoint)
      functions executionFuel outputFuel publicCompletion invocation) := by
  obtain ⟨actual, generation, native, finalStore, completed, exported, atReturned⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, size, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.completed_reflects functions profile receiver extension bodyTyping wellFormed
      history.semantic entry inHistory entryType sourceEq retained input started parameterView metadata completed invocation
  obtain ⟨payload, decoded, _imported⟩ := exported.reimports
  obtain ⟨source, outcomeEq, _represented, _heaps, _world, _returned, _related, _stable, _heapTyped, _typed⟩ :=
    CellAwarePublicApplicationResult.returned_value resultAt decoded
  subst outcome
  obtain ⟨reached, related, retainedHistory⟩ := history.semantic.after_packed_success started.original exported resultAt
  exact ⟨⟨actual, generation, native, finalStore, sources, packing, arity, size, source, after, finalMap, finalWorld,
    reached, completed, exported, atReturned, trace, trace.sound.value_plain, resultAt, related,
    ⟨retainedHistory, history.physical.extend resultAt.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady exportsReady)⟩⟩

structure Failed (executionFuel : Nat) (token : Word)
    (publicReturned : SourceCoreExecution.Session publicArtifact) (invocation : Staging.Recursive.Scope) where
  actual : Session artifact
  native : Core.Value
  finalStore : Store
  sources : List Dynamic.Value
  packing : Dynamic.ValuesPack sources packedSource
  arity : sources.length = function.parameters.length
  size : Nat
  failure : Staging.Recursive.Failure
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  reached : Caller headers keys finalMap finalWorld after finalStore
  completed : checkpoint.NativeDone executionFuel native finalStore
  failed : checkpoint.FailedResultAt executionFuel native finalStore token actual
  atSession : publicReturned.IndexedAt actual
  trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages size invocation
    anchor.function.context before entry.source sources (.fault failure) after
  plain : ∀ reason, failure = .semantic reason →
    Dynamic.CallableFaults (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source) before entry.source sources reason after
  result : ResultAt (registry := completion.result.context.registry) functions rootCells caller anchor.function.context result nativeResult
    (.fault failure) after native finalStore finalMap finalWorld callFaults
  fault : callFaults failure token
  heap : Dynamic.HeapWellTyped anchor.function.context after
  related : CallableIndexedOwnedFunctionState.Relates caller reached
  history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := rootCells)
    (receiving := completion.result.context.registry) (anchor := anchor)
    actual finalMap finalWorld after finalStore reached entries
  registry : actual.RegistryAt completion.result.context.registry
  exports : publicReturned.ExportsReady

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started
  parameterView metadata atCheckpoint exactRegistry exportsReady in
/-- The failed public event recovers its real staged fault and reached heap.
When the fault is semantic, erasure yields the independent Source fault. -/
theorem failed {executionFuel outputFuel : Nat} {token : Word}
    {publicReturned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token publicReturned))
    (invocation : Staging.Recursive.Scope) :
    Nonempty (Failed (completion := completion) (caller := caller) (anchor := anchor) (result := result) (function := function) (packedSource := packedSource)
      (entry := entry) (entries := entries) (nativeResult := nativeResult) (checkpoint := checkpoint)
      functions executionFuel token publicReturned invocation) := by
  obtain ⟨actual, _generation, native, finalStore, completed, failedAt, atReturned⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨sources, packing, arity, size, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.completed_reflects functions profile receiver extension bodyTyping wellFormed
      history.semantic entry inHistory entryType sourceEq retained input started parameterView metadata completed invocation
  obtain ⟨failure, outcomeEq, fault⟩ : ∃ failure, outcome = .fault failure ∧ callFaults failure token := by
    have related := resultAt.1
    have decoded := failedAt.2.1
    cases related with
    | value _ => cases decoded
    | fault related =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        subst token
        exact ⟨_, rfl, related⟩
  subst outcome
  have afterTyped := CellAwarePublicMaterializedFaultHeap.after_fault functions bodyTyping wellFormed history.semantic
    entry inHistory entryType input started parameterView metadata packing trace
  obtain ⟨reached, related, retainedHistory⟩ := history.semantic.after_packed_failure
    started.original failedAt resultAt afterTyped
  have returnedRegistry : actual.RegistryAt completion.result.context.registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨⟨actual, native, finalStore, sources, packing, arity, size, failure, after, finalMap, finalWorld,
    reached, completed, failedAt, atReturned, trace,
    (fun reason same => (same ▸ trace.sound).semanticFault_plain), resultAt, fault, afterTyped, related,
    ⟨retainedHistory, history.physical.extend resultAt.2.2.2.2.1⟩, returnedRegistry,
    atReturned.exportsReady_iff.mpr (failedAt.exportsReady
      (started.original.initial_registry.exportsReady exportsReady))⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedForward
/-! Ordinary Source application reaches genuine public success from the
actual retained export, accepted packed request and current physical history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedForward
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
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

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq retained input started parameterView metadata
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
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwareSelectedPublicRetainedMaterializedHandle.source_has_sufficient_fuel (invocation := invocation)
      functions profile receiver extension bodyTyping selectedBodies history entry inHistory entryType sourceEq retained
      input started parameterView metadata packing arity trace
  obtain ⟨requiredOutput, exported⟩ := CellAwarePublicDirectOutput.after_success functions cellModel started
    exactRegistry resultView ready atCheckpoint semantic runs ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, semantic, exported⟩

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq retained input started parameterView metadata
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
  obtain ⟨owner, bindings, parameterCore, resultCore, association, _framed⟩ := retained.association sourceEq
  have frame := CellAwareSelectedPublicRetainedMaterializedHandle.source_frame functions bodyTyping history
    entry inHistory entryType sourceEq
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (.fault (.semantic reason)) after := by
    rw [sourceEq] at trace ⊢
    exact GeneralizedLocalSourceApplicationLifting.selected_association_exact association frame selectedBodies
      (CellAwareSelectedPublicMaterializedHandleMeaning.source_arguments functions bodyTyping history entry inHistory
        entryType sourceEq input started parameterView metadata packing arity) arity.symm trace
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  have heapTyped := CellAwareSelectedPublicMaterializedFaultHeap.after_fault functions bodyTyping selectedBodies history
    entry inHistory entryType input started parameterView metadata packing measured
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwareSelectedPublicRetainedMaterializedHandle.source_has_sufficient_fuel (invocation := invocation)
      functions profile receiver extension bodyTyping selectedBodies history entry inHistory entryType sourceEq retained
      input started parameterView metadata packing arity trace
  obtain ⟨token, fault, failed⟩ := CellAwarePublicDirectFailure.after_failure functions cellModel started
    exactRegistry ready atCheckpoint semantic runs heapTyped ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, token, semantic, fault, failed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareCheckedPublicRetainedMaterializedForward
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareProfiledPublicRetainedMaterializedForward
/-! Ordinary Source application reaches genuine public success from the
actual retained export, accepted packed request and current physical history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareProfiledPublicRetainedMaterializedForward
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
  (issued : SelectedCompilationCertifiedPublicSession.Profiled recipe)
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
    issued.support.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
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
    issued.support.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
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
    issued.support.bodyTyping issued.registryBodies history entry inHistory entryType sourceEq retained
    input started parameterView metadata completed invocation

end Solcore.SourceSemantics.CoreLowering.CellAwareProfiledPublicRetainedMaterializedForward
end
