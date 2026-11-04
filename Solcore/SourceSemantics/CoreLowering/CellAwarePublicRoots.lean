import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation

/-!
# Cell-aware public roots

The unchanged public root runs its argument packing, the stored named closure and the
body, for each family of cell-aware bodies with a finite profile: named, lexical,
faulting, imperative and materialized. Each family states the same four theorems.

Main declarations:
- `CellAwarePublicNamedRoot.preserves_root` and `CellAwarePublicNamedRoot.reflects_root`,
  the two directions at the root;
- `CellAwarePublicNamedRoot.checkpoint_has_sufficient_fuel` and
  `CellAwarePublicNamedRoot.checkpoint_reflects`, the same at the actual checkpoint;
- `CellAwarePublicLexicalNamedRoot.checkpoint_reflects`,
  `CellAwarePublicFaultingNamedRoot.checkpoint_reflects` and
  `CellAwarePublicImperativeNamedRoot.checkpoint_reflects`, the other families;
- `CellAwarePublicNamedSource.preserves_root` and
  `CellAwarePublicImperativeSourceRoot.preserves_root`, from an independent Source trace.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedRoot
/-! The unchanged public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedRoot
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
  obtain ⟨packet⟩ := CellAwareNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨value, finalStore, finalMap, finalWorld, result, _effect⟩ :=
    CellAwareNamedInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
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
  obtain ⟨packet⟩ := CellAwareNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
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
    CellAwareNamedInvocation.reflects_selected callableProfile receiver extension owner caller header capture.named
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

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalNamedRoot
/-! The unchanged interleaved public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalNamedRoot
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
  obtain ⟨packet⟩ := CellAwareLexicalNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨value, finalStore, finalMap, finalWorld, result, _effect⟩ :=
    CellAwareLexicalNamedInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
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
  obtain ⟨packet⟩ := CellAwareLexicalNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
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
    CellAwareLexicalNamedInvocation.reflects_selected callableProfile receiver extension owner caller header capture.named
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

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalNamedRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingNamedRoot
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedRoot
/-! The unchanged public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedRoot
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
  obtain ⟨packet⟩ := CellAwareImperativeNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨value, finalStore, finalMap, finalWorld, result, _effect⟩ :=
    CellAwareImperativeNamedInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.issued packet.body packet.projection support
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
  obtain ⟨packet⟩ := CellAwareImperativeNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
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
    CellAwareImperativeNamedInvocation.reflects_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.issued packet.body packet.projection support
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

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedNamedRoot
/-! The unchanged public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedNamedRoot
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
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {recipe : SourceCoreIndexedSession.Recipe}
  (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  (bodyProfile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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

include aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected represented heaps in
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
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareMaterializedNamedPreparedReceipt.of_header prepared aligned capture ready diagnostic wellFormed
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨value, finalStore, finalMap, finalWorld, result, output, _effect⟩ :=
    CellAwareMaterializedNamedInvocation.preserves callableProfile owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      packet.issuer packet.body wellFormed
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
  exact ⟨capture.named, value, finalStore, finalMap, finalWorld, required, run, result, output⟩

variable {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {inputFuel : Nat}
  (sameCompiled : recipe.compiled = whole)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments inputFuel
    nativeCheckpoint recipe (sameCompiled.symm ▸ root) world store payloads encodedValues)

include aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected represented heaps sameCompiled started in
/-- The actual public start uses the same root and captured cache. Sufficient
execution fuel follows the independent Source derivation. -/
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
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result, output⟩ :=
    preserves_root callableProfile prepared aligned ready diagnostic wellFormed bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped bodySelected
      represented heaps allocated trace
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result, output⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedNamedRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedSource
/-! The actual public root is driven by an independent ordinary Source body.
Every stage guard is checked by the real lifting; an earlier rejection retains
its reached heap through BodyAdapted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedSource
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
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareNamedSourceInvocation.lift_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨actualCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicNamedRoot.preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, actualCapture, value, finalStore, finalMap, finalWorld,
    required, adapted, run, result⟩

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
theorem checkpoint_has_sufficient_fuel_selected
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
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
      required, adapted, run, result⟩ :=
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
    required, adapted, fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

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
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFaultSource
/-! Source-driven public execution retains deep heap typing at its actual
fault endpoint, including stage rejection before the original Source outcome. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFaultSource
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
  obtain ⟨packet⟩ := CellAwareNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareNamedSourceInvocation.lift_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨actualCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicNamedRoot.preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, actualCapture, value, finalStore, finalMap, finalWorld,
    required, adapted, (by intro failure same; subst stagedOutcome; exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated measured), run, result⟩

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
theorem checkpoint_has_sufficient_fuel_selected
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
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
    required, adapted, faultHeap, fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

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
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFaultSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalSourceRoot
/-! The unchanged interleaved public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalSourceRoot
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
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareLexicalNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, _effect⟩ :=
    CellAwareLexicalNamedSourceInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
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
  exact ⟨capture.named, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result⟩

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
/-- The actual public start uses the same root and captured cache. The independent
Source body supplies sufficient execution fuel, with an explicit reached stage stop. -/
theorem checkpoint_has_sufficient_fuel_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result⟩ :=
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_has_sufficient_fuel
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalSourceRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFaultSource
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
  obtain ⟨packet⟩ := CellAwareLexicalNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareLexicalNamedSourceInvocation.lift_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨actualCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicLexicalNamedRoot.preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, actualCapture, value, finalStore, finalMap, finalWorld,
    required, adapted, (by intro failure same; subst stagedOutcome; exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated measured), run, result⟩

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
theorem checkpoint_has_sufficient_fuel_selected
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
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
    required, adapted, faultHeap, fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

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
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalFaultSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFaultSource
/-! Source-driven public execution retains deep heap typing at its actual
fault endpoint, including stage rejection before the original Source outcome. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFaultSource
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
  obtain ⟨packet⟩ := CellAwareFaultingNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareFaultingNamedSourceInvocation.lift_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.body support
      stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨actualCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    CellAwarePublicFaultingNamedRoot.preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic
      support bodyProfile selected owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped
      sidecarIssued bodySelected represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, actualCapture, value, finalStore, finalMap, finalWorld,
    required, adapted, (by intro failure same; subst stagedOutcome; exact CellAwareNamedFaultHeap.after_fault_selected header support bodySelected heapTyped argumentsTyped allocated measured), run, result⟩

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
theorem checkpoint_has_sufficient_fuel_selected
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
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨stagedContext, stagedOutcome, reached, capture, value, finalStore, finalMap, finalWorld,
    required, adapted, faultHeap, fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
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
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

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
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFaultSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeSourceRoot
/-! The unchanged imperative public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeSourceRoot
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
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareImperativeNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, _effect⟩ :=
    CellAwareImperativeNamedSourceInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
      packet.generation record aligned.layouts aligned.globals sameBindings packet.emitted sameSolved bodySelected
      (CellAwareNamedCallAuthority.of_header header sidecarIssued) packet.issuer packet.issued packet.body packet.projection support
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
  exact ⟨capture.named, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result⟩

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
/-- The actual public start uses the same root and captured cache. The independent
Source body supplies sufficient execution fuel, with an explicit reached stage stop. -/
theorem checkpoint_has_sufficient_fuel_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result⟩ :=
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_has_sufficient_fuel
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults := by
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeSourceRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedSourceRoot
/-! The unchanged interleaved public root executes its actual argument packing, stored
named closure and mixed body. Its finite profile is used only to construct
compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedSourceRoot
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
  (bodyProfile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
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
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨packet⟩ := CellAwareMaterializedNamedPreparedReceipt.of_header_selected prepared aligned capture ready diagnostic support.bodyTyping
    entryMember bodyProfile
  have record := CallableIndexedActualNamedSourceReceipts.header_record whole header
  have sameBindings : header.bindings = header.named.inputs := by rw [aligned.bindings, aligned.named]
  have sameSolved : header.solved = header.named.specialized.function.solvedRequirements := by rw [aligned.solved, aligned.named]
  obtain ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, output, _effect⟩ :=
    CellAwareMaterializedNamedSourceInvocation.preserves_selected callableProfile receiver extension owner caller header capture.named
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
  exact ⟨capture.named, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result, output⟩

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
/-- The actual public start uses the same root and captured cache. The independent
Source body supplies sufficient execution fuel, with an explicit reached stage stop. -/
theorem checkpoint_has_sufficient_fuel_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value := by
  cases sameCompiled
  obtain ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted, run, result, output⟩ :=
    preserves_root_selected callableProfile receiver extension prepared aligned ready diagnostic support bodyProfile selected
      owner caller globalReference keyPhysical physical stable heapTyped argumentsTyped sidecarIssued bodySelected
      represented heaps allocated trace
  exact ⟨capture, stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, required, adapted,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result, output⟩


/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps in
theorem preserves_root
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value := by
  apply preserves_root_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) <;> assumption

include receiver extension aligned ready diagnostic wellFormed bodyProfile selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped sidecarIssued bodySelected represented heaps sameCompiled started in
theorem checkpoint_has_sufficient_fuel
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size header.context
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence
      (RecursiveStageRegistry.scope sidecar [] header.function).source environment bound
      header.function.body finalContext outcome after) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld required,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      (∀ fuel, required ≤ fuel → nativeCheckpoint.NativeDone fuel value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value := by
  apply checkpoint_has_sufficient_fuel_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (receiver := receiver) (extension := extension) (aligned := aligned) (ready := ready) (diagnostic := diagnostic) (bodyProfile := bodyProfile) (selected := selected) (globalReference := globalReference) (keyPhysical := keyPhysical) (physical := physical) (stable := stable) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (sidecarIssued := sidecarIssued) (bodySelected := bodySelected) (represented := represented) (heaps := heaps) (sameCompiled := sameCompiled) (started := started) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedSourceRoot
end
