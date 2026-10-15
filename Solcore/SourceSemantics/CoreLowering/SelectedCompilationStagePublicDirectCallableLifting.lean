import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectNamedBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure

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
