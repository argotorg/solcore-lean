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
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
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
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function parameter result) (.closure function) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
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
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association callStages, SupportFor association callStages packet :=
    fun association => Classical.choice
      (CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.sequence_coverage stagePrepared family
        (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed association)
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := callStages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) rfl
  have canonicalBodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages semanticFaults callFaults childSize :=
    CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects_canonical
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) rfl
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed
  obtain ⟨sources, values, packing, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
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
    exact application_tail completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds.application_reflects (semantic := semantic)
      profile association (chosen association).1 (chosen association).2 caller raw represented heaps stable runtime
      valid size (fun childSize _ => bodies childSize) (fun childSize _ => canonicalBodies childSize) evaluation (Nat.le_refl _)
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
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
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association callStages, SupportFor association callStages packet :=
    fun association => Classical.choice
      (CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.sequence_coverage stagePrepared family
        (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed association)
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := callStages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic)
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have canonicalBodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages semanticFaults callFaults childSize :=
    CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves_canonical
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic)
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed

  obtain ⟨decodedSources, values, decodedPacking, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
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
    CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds.application_preserves (semantic := semantic)
      profile association (chosen association).1 (chosen association).2 caller raw represented heaps stable runtime
      sourceSize (fun childSize _ => bodies childSize) (fun childSize _ => canonicalBodies childSize) trace (Nat.le_refl _)
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [nativeEq]
    exact application_tail measured
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨value, finalStore, finalMap, finalWorld, padded.sound,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end Packed
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
