import Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalNamedRoot
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap

/-! Source-driven public execution retains deep heap typing at its actual
fault endpoint, including stage rejection before the original Source outcome. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFaultSource
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

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)
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


include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached,
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ failure, stagedOutcome = .fault failure → Dynamic.HeapWellTyped header.context reached) ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareLexicalNamedPreparedReceipt.of_header prepared aligned capture ready diagnostic wellFormed
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareLexicalNamedSourceInvocation.lift callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body wellFormed
      stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨actualCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicLexicalNamedRoot.preserves_root callableProfile receiver extension prepared aligned ready diagnostic
      wellFormed bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, actualCapture, value, finalStore, finalMap, finalWorld,
    required, adapted, (by intro failure same; subst stagedOutcome; exact CellAwareNamedFaultHeap.after_fault header wellFormed bodySelected heapTyped argumentsTyped allocated measured), run, result⟩

variable {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {inputFuel : Nat}
  (sameCompiled : recipe.compiled = whole)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments inputFuel
    nativeCheckpoint recipe (sameCompiled.symm ▸ root) world store payloads encodedValues)

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_has_sufficient_fuel
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached,
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ failure, stagedOutcome = .fault failure → Dynamic.HeapWellTyped header.context reached) ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, faultHeap, run, result⟩ :=
    preserves_root callableProfile receiver extension prepared aligned ready diagnostic wellFormed bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
    required, adapted, faultHeap, fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFaultSource
