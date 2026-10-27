import Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedRoot
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallEntry

/-! The unchanged public root of a call-containing named row. The root
executes its actual argument packing and stored named closure; the body runs on
the slot-retaining protocol from the root's physical cache and capture
(`CellAwareInvocationAcceptedCallEntry`). The body's accepted-expression meaning
is the input that the family induction
(`CellAwareInvocationAcceptedCallFamily.expressions`) supplies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedCallRoot
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

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions)
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected artifact checked covered represented heaps in
/-- An independent Source trace of a call-containing body determines the
actual root execution and the restored caller, given the body's
accepted-expression meaning on the slot-retaining protocol. -/
theorem preserves_root_selected
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size
      (RecursiveStageRegistry.scope sidecar [] header.function) header.context environment bound
      header.function.body finalContext outcome after)
    (expressions : ∀ (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (index prepared aligned) stages child faults size) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment whole.indexed) store) =
        .done value finalStore) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        rootFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨_source, _signatures, _typing, projection, native⟩ :=
    CellAwareInvocationAcceptedNamedHeaders.static_inputs prepared aligned ready entryMember (support.certified header)
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CellAwareInvocationAcceptedCallEntry.preserves_selected callableProfile receiver header prepared.compilation
      (CellAwareInvocationAcceptedNamedHeaders.record prepared aligned) aligned.named aligned.layouts
      aligned.globals aligned.bindings aligned.body aligned.solved projection support
      (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic)
      (CallableIndexedOwnedPublicDiagnosticReceipts.assignments_prepared prepared diagnostic)
      artifact checked body covered native owner caller capture physical stable heapTyped argumentsTyped represented
      (heaps.includes CellAwareInvocationAcceptedNamedInvocation.cell_of_profiled) bodySelected allocated trace
      expressions
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

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedCallRoot
