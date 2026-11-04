import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.AcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedCalls

/-!
# Accepted bodies at the public root

The strongest results of the accepted-body route: an accepted body, related to the
native completion of the actual public start, through the unchanged public root.

Main declarations:
- `CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected` and
  `CellAwarePublicAcceptedNamedRoot.checkpoint_reflects_selected`, both directions;
- `CellAwarePublicAcceptedNamedForward.first_value_selected`, from a staged trace that
  returns a value to a successful public resumption;
- `CellAwarePublicAcceptedCallRoot.preserves_root_selected`, the same preservation for a
  row whose body contains direct calls;
- `CellAwarePublicAcceptedNamedRoot.compilation_receipts` and
  `CellAwarePublicAcceptedNamedRoot.refined_body`, which derive the static receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedRoot
/-! The unchanged public root executes its actual argument packing, stored
named closure and accepted body. The body's own accepted-body index, its
static inputs and its read and write inputs come from the actual prepared
header and public diagnostic receipt; the closed expression subset, statement
coverage and the original compilation receipt remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedRoot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwareInvocationAcceptedNamedHeaders (index)

/-- The original compilation receipt of the theorems below comes from the
actual checked program, its public compilation and the issued recipe. -/
theorem compilation_receipts {recipe : SourceCoreIndexedSession.Recipe}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {options : SourceCompiler.Options} {facade : SourceCompiler.Compiled}
    (accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe) :
    ∃ sourceCompiled : SourceCoreCompiler.Compiled,
      sourceCompiled.artifact? = some recipe.compiled ∧ checkProgram raw checkingFuel = .ok sourceCompiled.program := by
  obtain ⟨source, generated, present, _ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation accepted selected
  refine ⟨source, present, ?_⟩
  rw [SourceCoreCompiler.compileChecked_program generated]
  exact checked

/-- The accepted body receipt of a prepared header, refined so that every
assignment the compiler supports carries its receipt. -/
theorem refined_body {whole : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row) {instantiation : DeclarationInstantiation}
    {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    ∃ body : AcceptedNamedBodyFlow.Body (index prepared aligned).policy (index prepared aligned).fuel
        (index prepared aligned).compilerSource (index prepared aligned).scope (index prepared aligned).statements
        (index prepared aligned).result (index prepared aligned).reasonAt (index prepared aligned).fellThrough
        (index prepared aligned).escaped (index prepared aligned).body,
      body.tree.Ready := by
  obtain ⟨body⟩ := (index prepared aligned).body_receipt
  obtain ⟨tree, ready⟩ := body.tree.refine (index prepared aligned).assignment_policy
    (index prepared aligned).bitNot_policy (RecursiveNamedPreparedHeaderPolicies.Prepared.match_success prepared)
  exact ⟨⟨body.flow, tree, body.emitted⟩, ready⟩

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

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults callableProfile
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions)
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include ready diagnostic support in
/-- The named row's static inputs, issuer and native typing at its installed
capture. -/
private theorem header_inputs (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header
      mapping world store)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts} (entryMember : entry ∈ whole.indexed.entries) :
    whole.compatible.checked.catalog.project header.function.resultType = .ok prepared.named.signature.resultType ∧
    CellAwareNamedDiagnosticIssuer.Named whole.indexed prepared.named
      (prepared.diagnostics.reasonAt prepared.named.signature.key) ∧
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (index prepared aligned).scope ++
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative))
      (index prepared aligned).body nativeType whole.indexed.layouts.definitions := by
  obtain ⟨_source, _signatures, _typing, projection, nativeType, nativeTyped⟩ :=
    CellAwareInvocationAcceptedNamedHeaders.static_inputs prepared aligned ready entryMember (support.certified header)
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, CellAwareNamedPreparedReceipt.administrative capture,
      header.parameterType, List.cons_append]
  rw [prefixEq] at nativeTyped
  have issuer := CellAwareNamedDiagnosticIssuer.of_prepared prepared diagnostic aligned
  rw [aligned.reasonAt, aligned.named] at issuer
  exact ⟨projection, issuer, nativeType, nativeTyped⟩

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected closed artifact checked covered represented heaps in
/-- An independent Source trace of the accepted body determines the actual root
execution and the restored caller. -/
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
        rootFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨projection, issuer, native⟩ :=
    header_inputs prepared aligned ready diagnostic support owner capture entryMember
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CellAwareInvocationAcceptedNamedInvocation.preserves_selected callableProfile receiver owner caller header capture.named
      prepared.compilation (CellAwareInvocationAcceptedNamedHeaders.record prepared aligned) aligned.named aligned.layouts
      aligned.globals aligned.bindings aligned.body aligned.solved bodySelected issuer projection support closed
      (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic)
      (CallableIndexedOwnedPublicDiagnosticReceipts.assignments_prepared prepared diagnostic)
      artifact checked body covered native stable heapTyped argumentsTyped represented heaps allocated trace
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

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected closed artifact checked covered represented heaps in
/-- Actual completion of the root reconstructs an independent Source execution
of the accepted body with the restored caller. -/
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
        rootFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt prepared aligned selected.member
    keyPhysical physical heaps.runtime_hasTypes
  obtain ⟨entry, entryMember, _shape, _first⟩ := selected.2
  obtain ⟨projection, issuer, native⟩ :=
    header_inputs prepared aligned ready diagnostic support owner capture entryMember
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
      allocated, trace, matched, result⟩ :=
    CellAwareInvocationAcceptedNamedInvocation.reflects_selected callableProfile receiver owner caller header capture.named
      prepared.compilation (CellAwareInvocationAcceptedNamedHeaders.record prepared aligned) aligned.named aligned.layouts
      aligned.globals aligned.bindings aligned.body aligned.solved bodySelected issuer projection support closed
      (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic)
      (CallableIndexedOwnedPublicDiagnosticReceipts.assignments_prepared prepared diagnostic)
      artifact checked body covered native stable heapTyped argumentsTyped represented heaps bodyEvaluation.sound
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

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected closed artifact checked covered represented heaps
  sameCompiled started in
/-- The actual public start uses the same root and captured cache. Sufficient
execution fuel follows the independent Source derivation of the accepted body. -/
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
        rootFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result⟩ :=
    preserves_root_selected callableProfile receiver prepared aligned ready diagnostic support selected owner caller
      globalReference keyPhysical physical stable heapTyped argumentsTyped bodySelected closed
      artifact checked body covered represented heaps allocated trace
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => started.initial.native_done_iff.mpr (run fuel enough), result⟩

include callableProfile receiver aligned ready diagnostic support selected globalReference keyPhysical physical
  stable heapTyped argumentsTyped bodySelected closed artifact checked covered represented heaps
  sameCompiled started in
/-- Actual native completion at the public checkpoint reconstructs an
independent Source execution of the accepted body. -/
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
        rootFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  cases sameCompiled
  exact reflects_root_selected callableProfile receiver prepared aligned ready diagnostic support selected owner caller
    globalReference keyPhysical physical stable heapTyped argumentsTyped bodySelected closed
    artifact checked body covered represented heaps (started.initial.native_done_iff.mp completed)

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedForward
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedCallRoot
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
end
