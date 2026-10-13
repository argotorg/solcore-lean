import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
import Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments

/-! Direct packed inputs are split using the real retained Source binder row.
The zero, singleton and longer cases retain exact grouping and argument order,
including nested functions, nominal metadata and mapping payloads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)


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
  {function : Dynamic.Closure} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) (.closure function) native
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
/-- The retained closure's actual binder row determines the source argument
vector, including the distinction between zero arguments and one Unit argument.
The existing numeric body family reflects the same complete native application. -/
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.closure function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have children : ∀ childSize,
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        callFaults childSize :=
    SelectedCompilationPhysicalMixedCallerFamily.reflects_with_methods
      receiver (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
      support.profile support.bodyTyping support.certificates (SelectedCompilationPhysicalProgramSupport.observations support) (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
      (SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension) support.bodies support.bodySupport
      support.closurePackets support.closureSupport support.owners support.methods rfl
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.closure_member support.profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.original.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed
  obtain ⟨sources, values, packing, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.original.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.original.source_binders
  have arity : sources.length = function.parameters.length := represented.length.1.symm.trans binderLength
  have argumentsTyped := packing.unpackTypes
    (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    argumentsTyped packing parameterEq.symm arity
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← nativeEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_reflects
      support.profile association (support.closurePackets association) (support.closureSupport association)
      caller raw represented heaps physical support.owners stable runtime
      valid size (fun childSize _ => children childSize) evaluation (Nat.le_refl _)
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- A Source application of the exact packed input constructs finite native
execution at the original caller store. The real Source arity disambiguates
zero, singleton and longer packs before the existing body preservation proof. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.closure function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have children : ∀ childSize,
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        callFaults childSize :=
    SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
      receiver (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
      support.profile support.bodyTyping support.certificates (SelectedCompilationPhysicalProgramSupport.observations support) (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
      (SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension) support.bodies support.bodySupport
      support.closurePackets support.closureSupport support.owners support.methods
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.closure_member support.profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.original.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed

  obtain ⟨decodedSources, values, decodedPacking, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.original.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.original.source_binders
  have decodedArity : decodedSources.length = function.parameters.length :=
    represented.length.1.symm.trans binderLength
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (decodedArity.trans arity.symm)
  subst decodedSources
  have argumentsTyped := packing.unpackTypes
    (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    argumentsTyped packing parameterEq.symm arity
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_preserves
      support.profile association (support.closurePackets association) (support.closureSupport association)
      caller raw represented heaps physical support.owners stable runtime
      sourceSize (fun childSize _ => children childSize) trace (Nat.le_refl _)
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [nativeEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨value, finalStore, finalMap, finalWorld, padded.sound,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
