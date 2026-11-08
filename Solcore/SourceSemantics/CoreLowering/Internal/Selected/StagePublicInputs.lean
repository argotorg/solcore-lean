import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageCalls
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.PublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions

/-!
# Lifting to staged Source: public inputs

Lifting of public inputs and whole programs, for initial data and for direct callable inputs.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open SelectedCompilationPublicSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages Support)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- An independent ordinary application uses the original named row and full
caller and invocation dictionaries. Its final heap is part of the judgment. -/
def PlainCall (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments outcome after

theorem plain_value {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (trace : PlainValue anchor header invocation before arguments value after) :
    PlainCall anchor header invocation before arguments (.value value) after := by
  obtain ⟨rawD, function, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, .value applied⟩

theorem plain_fault {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (trace : PlainFault anchor header invocation before arguments reason after) :
    PlainCall anchor header invocation before arguments (.fault reason) after := by
  obtain ⟨rawD, function, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, .fault applied⟩

/-- Internal selected-body port. The closed root family supplies this port;
public callers supply only their original Source trace and actual input receipts. -/
def NamedBodies (support : Support compiled (headers rows) (keys compiled) initial) : Prop :=
  ∀ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed),
    CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
      receiving.result.context.registry receiving.result.extension receiving.result.diagnostics →
    SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry →
    ∀ (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers rows →
    ∀ budget {child : Staging.Recursive.Scope}, (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers rows) (keys := keys compiled) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry
          (SelectedCompilationPhysicalProgramSupport.functions support)) (stages compiled) child budget

/-- Actual startup and retained history derive all argument, heap and capture
preconditions at the input registry before lifting the ordinary application. -/
theorem lift_call_at_input_registry (support : Support compiled (headers rows) (keys compiled) initial)
    (bodies : NamedBodies support)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor request.header invocation state.heap arguments plain after) :
    ∃ staged reached, SourceCall anchor request.header invocation state.heap arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile) (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadata)
  obtain ⟨rawD, function, sourceAt, plainTrace⟩ := trace
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size plainTrace
  let packet := support.bodies request.header request.selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt packet.prepared packet.aligned
    request.selected.member (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
    history.physical heaps.runtime_hasTypes
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor request.header
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected
      sourceAt packet.prepared packet.aligned (stagePrepared recipe.compiled) descriptor
  have selected : (stages recipe.compiled).Closure request.header.function
      (RecursiveStageRegistry.scope sidecar [] request.header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.lifts_invocation
      (functions := functions rows initial profile) (registry := receiving.result.context.registry)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (caller := state.caller) (header := request.header) (physicalCapture := capture) (sourceAt := sourceAt)
      packet.layouts history.physical request.selected.member support.bodyTyping.function_ids
      (support.certificates request.header request.selected.member) stable heapTyped argumentsTyped represented heaps
      selected size (bodies receiving issued extension request.header request.selected.member size selected)
      measured (Nat.le_refl _)
  obtain ⟨stagedSize, stagedTrace⟩ := Staging.Recursive.Size.Applies.of_trace lifted
  exact ⟨staged, reached, ⟨rawD, function, stagedSize, sourceAt, stagedTrace⟩, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared stages)
open SelectedCompilationStagePublicInputLifting (PlainCall NamedBodies)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem lift_call
    (bodies : NamedBodies support)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached, SourceCall anchor header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := receiving)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceAt, plainTrace⟩ := trace
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size plainTrace
  let packet := support.bodies header start.selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt packet.prepared packet.aligned
    start.selected.member (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
    caller.physical heaps.runtime_hasTypes
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor header
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected
      sourceAt packet.prepared packet.aligned (stagePrepared recipe.compiled) descriptor
  have selected : (stages recipe.compiled).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.lifts_invocation
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (registry := receiving.result.context.registry)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (caller := caller.base.val) (header := header) (physicalCapture := capture) (sourceAt := sourceAt)
      packet.layouts caller.physical start.selected.member support.bodyTyping.function_ids
      (support.certificates header start.selected.member) stable heapTyped argumentsTyped represented heaps
      selected size (bodies receiving receiverIssued receiverExtension header start.selected.member size selected)
      measured (Nat.le_refl _)
  obtain ⟨stagedSize, stagedTrace⟩ := Staging.Recursive.Size.Applies.of_trace lifted
  exact ⟨staged, reached, ⟨rawD, function, stagedSize, sourceAt, stagedTrace⟩, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared stages)
open SelectedCompilationStagePublicInputLifting (PlainCall NamedBodies)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem lift_call
    (bodies : NamedBodies support)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached, SourceCall anchor header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  have _ := simple
  exact SelectedCompilationStageInitialDataInputLifting.lift_call
    rows prepared anchor header support bodies distinct call start inputTypes inputMeanings trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialInputLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectCallableLifting
/-! A retained callable selects its actual source body and complete stored
capture. The real packed parameter row supplies entry arguments before the
closed ordinary-to-staged body family is applied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectCallableLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Value} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before function (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) function native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
theorem lifts_packed {invocation : Staging.Recursive.Scope}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) function sources.length)
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      (Staging.Recursive.callableEvidence function) before function sources plain after) :
    Staging.Recursive.Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) callStages
      invocation context before function sources plain after := by
  classical
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size called
  cases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure function =>
      obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
        CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.closure_member support.profile calleeRelated function rfl
      obtain ⟨parameterEq, _resultEq, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
      have sourceBundle : parameter = TypeSystem.Ty.productMany
          (bindings.map (fun binding => binding.1.scheme.body)) := by
        rw [association.source_binders]
        exact parameterEq
      have packed := packedRelated
      rw [sourceBundle] at packed
      obtain ⟨decodedSources, values, decodedPacking, _nativeEq, represented⟩ :=
        RecursivePublicPackedArguments.arguments bindings association.projected_bindings packed
      have actualArity : sources.length = function.parameters.length := arity.closure_count.symm
      have binderLength : bindings.length = function.parameters.length := by
        simpa only [List.length_map] using congrArg List.length association.source_binders
      have decodedArity : decodedSources.length = function.parameters.length :=
        represented.length.1.symm.trans binderLength
      have sameSources : decodedSources = sources :=
        decodedPacking.injective_of_length_eq packing (decodedArity.trans actualArity.symm)
      subst decodedSources
      have argumentsTyped := packing.unpackTypes
        (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using actualArity)
      have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
        argumentsTyped packing parameterEq.symm actualArity
      have bodies := SelectedCompilationStageClosurePacketRoots.association_of_roots (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed) (observations := SelectedCompilationPhysicalProgramSupport.observations support) (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) receiver) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension)
        functions association (support.closurePackets association)
        (support.closureSupport association) support.owners
        (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
        (budget := size)
        (fun childSize _ => SelectedCompilationStageActualLifting.lifts_roots support receiver extension childSize)
        (fun childSize => SelectedCompilationStageLiftBounds.preserves_roots support receiver extension childSize)
      exact SelectedCompilationStageClosurePacketLifting.application_lifts support.profile association
        (support.closurePackets association) (support.closureSupport association) caller raw represented heaps physical
        stable size bodies measured (Nat.le_refl _)
  | global function =>
      obtain ⟨_originalType, ⟨association⟩, _rawType⟩ :=
        CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member support.profile calleeRelated function rfl
      let header := association.header
      let sourceAt := association.sourceAt
      let packet := support.bodies header association.member
      obtain ⟨⟨capture, _captureEq⟩⟩ :=
        association.at_store packet.prepared packet.aligned (support.owners association.owner) physical
      have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters association.type_eq
      have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at sourceAt
        support.bodyTyping packet.prepared packet.aligned
      have headerCertified := support.certificates header association.member
      obtain ⟨facts, certified⟩ := certifiedAt
      have signature : parameter = TypeSystem.Ty.productMany header.types ∧ result = header.function.resultType := by
        rcases calleeTyped.global_inv with ordinary | staged
        · obtain ⟨typeEq, _valid, _evidence⟩ := ordinary
          have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
          exact ⟨signature.1, signature.2.trans sourceAt.frame.result.symm⟩
        · obtain ⟨inner, impossible, _typed⟩ := staged
          cases impossible
      have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
        have same := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
        rw [header.parameters] at same
        simpa only [List.map_map, Function.comp_def] using same.symm
      have packed := packedRelated
      rw [signature.1] at packed
      obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, _packedEq, packedType⟩ :=
        RecursivePublicPackedArguments.values header.types packed
      have typeLength : header.types.length = header.bindings.length := by rw [bindingTypes, List.length_map]
      have nativeRow : nativeTypesRow = header.bindings.map Prod.snd :=
        CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
          (by simpa only [List.length_map] using rows.length.2.2.symm.trans typeLength)
          (packedType.symm.trans (nativeTypes.1.trans header.parameterType))
      rw [bindingTypes, nativeRow] at rows
      have represented := RecursivePublicPackedArguments.of_values header.bindings rows
      have decodedArity : header.function.parameters.length = decodedSources.length := by
        simpa only [header.parameters, List.length_map] using represented.length.1
      have actualArity : header.function.parameters.length = sources.length := by
        have actual := SelectedCompilationPackedNamedArguments.global_count arity support.bodyTyping.function_ids sourceAt.frame.instantiated
        simpa only [header, sourceAt.frame.parameters] using actual
      have sameSources : decodedSources = sources :=
        decodedPacking.injective_of_length_eq packing (decodedArity.symm.trans actualArity)
      subst decodedSources
      obtain ⟨bodyHeap, argumentsTyped⟩ :=
        SelectedCompilationPackedNamedArguments.arguments_at_global
          sourceAt ⟨facts, certified⟩ runtime heapTyped calleeTyped packing packedTyped actualArity
      obtain ⟨sidecar, _prepared, _same, selected, _declaration, _local, _evidence, _marker, _analysis⟩ :=
        CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt packet.prepared packet.aligned
          (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) association.descriptor
      rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at selected
      have bodies : SelectedCompilationStageBodyLiftBounds.NamedLiftsBelow
          (headers := headers) (keys := keys) header
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          callStages (RecursiveStageRegistry.scope sidecar [] header.function) size :=
        SelectedCompilationStageNamedBodyLifting.lifts (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) receiver) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension) (support.bodySupport header association.member)
        support.profile headerCertified (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
        selected (budget := size)
        (fun childSize _ => SelectedCompilationStageActualLifting.lifts_roots support receiver extension childSize)
        (fun childSize => SelectedCompilationStageLiftBounds.preserves_roots support receiver extension childSize)
      exact SelectedCompilationStageNamedInvocationLifting.lifts_invocation functions association.owner caller
        header capture sourceAt packet.layouts physical association.member support.bodyTyping.function_ids headerCertified
        stable bodyHeap argumentsTyped represented heaps selected size bodies measured (Nat.le_refl _)
  | builtin function =>
      exact ⟨_, _, SelectedCompilationStageLiftBuiltin.builtin_application called, .completed⟩

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectCallableLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

/-- Ordinary successful application fixes the genuine unpacked arity. -/
theorem arity_of_value {program : Program} {context : Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function value : Dynamic.Value} {arguments : List Dynamic.Value}
    (trace : Dynamic.CallableApplies program context caller invocation before function arguments value after) :
    RecursivePublicCallableArity.Arity program function arguments.length := by
  cases trace with
  | builtin applied =>
    have length := (applied.preserves (context := context) (heap := before)).1.length_eq
    exact length ▸ .builtin _
  | global instantiates _ _ invoked =>
    cases invoked with
    | returned _ _ _ allocated _ _ => exact allocated.length_eq ▸ .global instantiates
    | unit _ _ _ _ allocated _ _ => exact allocated.length_eq ▸ .global instantiates
  | closure _ _ _ _ allocated _ _ => exact allocated.length_eq ▸ .closure _
  | closureUnit _ _ _ _ _ allocated _ _ => exact allocated.length_eq ▸ .closure _

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- The real packed input registry and retained history provide every physical
argument needed to lift an ordinary call through its complete callable value. -/
theorem lift_call
    (state : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok checkpoint)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram)
      entry.source sources.length)
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Outcome (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source sources plain after) :
    Staging.Recursive.Lifting.ApplicationLift (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
      anchor.function.context state.heap entry.source sources plain after := by
  obtain ⟨nativeCheckpoint, _atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  obtain ⟨receiving, _indexed, contextAt, receiver, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨currentImported, calleeRelated, calleeTyped⟩ := retained.current.2.2.2.2 entry member
  have callableEq := started.callable_eq currentImported
  rw [entryType] at calleeRelated calleeTyped
  rw [← callableEq] at calleeRelated
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    calleeRelated.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at calleeRelated
  obtain ⟨packedRelated, packedTyped⟩ :=
    started.history_input_compatible retained input parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := retained.current
  exact SelectedCompilationStagePublicDirectCallableLifting.lifts_packed
    issued.support receiver (state.extension.trans extended) state.caller state.history.physical stable
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping anchor)
    heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated packing arity trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPhysicalProgramSupport (Support)
open SelectedCompilationStagePublicInputLifting (NamedBodies)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}


/-- The closed induction supplies every reached named body from its authentic
compiler packet and checker-derived typing at the actual public registry. -/
theorem named_bodies (support : Support compiled (headers rows) (keys compiled) initial) :
    NamedBodies support := by
  intro receiving issued extension header member budget child selected
  exact SelectedCompilationStageNamedBodyLifting.lifts (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension) (support.bodySupport header member)
    support.profile (support.certificates header member) (SelectedCompilationPhysicalProgramSupport.static_extension support extension) selected
    (fun size _ => SelectedCompilationStageActualLifting.lifts_roots support issued extension size)
    (fun size => SelectedCompilationStageLiftBounds.preserves_roots support issued extension size)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicProgramLifting
end
