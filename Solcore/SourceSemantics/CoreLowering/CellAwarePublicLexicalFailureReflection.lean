import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicLexicalNamedRoot
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicResultContext
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues

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
