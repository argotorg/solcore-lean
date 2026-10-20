import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! The unchanged interleaved public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingNamedRoot
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

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareFaultingNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨value, finalStore, finalMap, finalWorld, result, _effect⟩ :=
    CellAwareFaultingNamedInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps allocated trace
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) globalReference
  have read := OptionalCell.read_success Word.zero
    (show Evaluates (DataPatternValues.packValues payloads :: payloads.reverse ++
        SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store
      (.var (header.slot + root.types.length + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) store
      from .var actualReference) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated read result.1
  have rootEvaluation : Evaluates
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store root.body value finalStore := by
    simpa only [selected.shape.2] using called
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel rootEvaluation
  exact ⟨capture.named, value, finalStore, finalMap, finalWorld, required, run, result⟩

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem reflects_root_selected
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
      .done value finalStore) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
        (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
        header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareFaultingNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) globalReference
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  rw [selected.shape.2] at measured
  obtain ⟨bodySize, _smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated actualReference capture.read measured
  obtain ⟨size, environment, bound, finalContext, outcome, after, finalMap, finalWorld,
      allocated, trace, matched, result, _effect⟩ :=
    CellAwareFaultingNamedInvocation.reflects_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps bodyEvaluation.sound
  exact ⟨capture.named, size, environment, bound, finalContext, outcome, after, finalMap, finalWorld,
    allocated, trace, matched, result⟩

variable {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {inputFuel : Nat}
  (sameCompiled : recipe.compiled = whole)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments inputFuel
    nativeCheckpoint recipe (sameCompiled.symm ▸ root) world store payloads encodedValues)

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
/-- The actual public start uses the same root and captured cache. Sufficient
execution fuel follows the independent Source derivation. -/
theorem checkpoint_has_sufficient_fuel_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

include receiver extension aligned ready diagnostic support bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_reflects_selected
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : nativeCheckpoint.NativeDone fuel value finalStore) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
        (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
        header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  exact reflects_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
    owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
    represented heaps (started.initial.native_done_iff.mp completed)

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem reflects_root
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
      .done value finalStore) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
        (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
        header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  apply reflects_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_has_sufficient_fuel
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_reflects
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : nativeCheckpoint.NativeDone fuel value finalStore) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
        (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
        header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  apply checkpoint_reflects_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingNamedRoot
