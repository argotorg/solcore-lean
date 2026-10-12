import Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedApplicationBounds
import Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedApplicationBounds

/-! A direct named handle keeps its genuine Header, Source dictionary and full
stored native capture. Packed inputs use that Header's actual parameter row;
the existing finite static family closes every nested body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectNamedApplicationBounds
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
  {function : Dynamic.GlobalFunction} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.global function) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function parameter result) (.global function) native
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
/-- Actual direct completion reflects the same global function, dictionary,
ordered arguments, captured native environment and full returned caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.global function) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.global function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  classical
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _rawType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨_facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
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
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values header.types packed
  have typeLength : header.types.length = header.bindings.length := by rw [bindingTypes, List.length_map]
  have nativeRow : nativeTypesRow = header.bindings.map Prod.snd :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (by simpa only [List.length_map] using rows.length.2.2.symm.trans typeLength)
      (packedType.symm.trans (nativeTypes.1.trans header.parameterType))
  rw [bindingTypes, nativeRow] at rows
  have represented := RecursivePublicPackedArguments.of_values header.bindings rows
  have arity : header.function.parameters.length = sources.length := by
    simpa only [header.parameters, List.length_map] using represented.length.1
  obtain ⟨bodyHeap, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime heapTyped calleeTyped packing packedTyped arity
  have supports := CallableIndexedOwnedPreparedStagedNamedArgumentRows.caller_supports sourceAt wellFormed runtime
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association callStages, SupportFor association callStages packet :=
    fun association => Classical.choice
      (CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.sequence_coverage stagePrepared family
        (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed association)
  let packet := namedTerminals header member
  have children : ∀ {child : Staging.Recursive.Scope}, (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
        (headers := headers) (keys := keys) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages child callFaults size := by
    intro child childSelected
    apply CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects
      (namedSupport header member) profile wellFormed childSelected
    intro childSize _smaller childContext childScope current id lowered root
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) rfl childSize root
  have evaluation : EvaluationSize size
      [CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
        (owner := owner) header capture identity descriptor.id, DataPatternValues.packValues values]
      store CallableIndexedLambdaCalls.applyPayload value finalStore := by
    have measured := RecursiveNamedPublicDirectClosureApplicationBounds.application_tail
      (other := []) completed
    rw [nativeEq, packedEq] at measured
    exact measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedNamedApplicationBounds.application_reflects
      functions owner caller header capture sourceAt packet.prepared packet.aligned stagePrepared descriptor packet.layouts member wellFormed
      stable bodyHeap argumentsTyped represented heaps supports identity descriptor.id size children evaluation (Nat.le_refl _)
  have actualResult : resultCore = header.output := nativeTypes.2.trans header.resultType
  have finalResult := resultAt.2
  rw [← signature.2, ← actualResult] at finalResult
  have count : header.sourceBody.source.inputs.length = sources.length := by
    rw [← sourceAt.frame.parameters]
    exact arity
  exact ⟨sources, packing, count ▸ RecursivePublicCallableArity.Arity.global sourceAt.frame.instantiated, sourceSize, outcome, after, finalMap, finalWorld, trace, finalResult⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.global function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
      wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  exact ⟨sources, packing, meaning⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- An independent named application at the authentic declared arity drives
the original native payload, retaining success or failure and the full caller post. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.global function) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.global function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  classical
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _rawType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨_facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
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
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
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
  have arity : header.function.parameters.length = sources.length := by
    have actual := arityAt.global_count wellFormed sourceAt.frame.instantiated
    simpa only [sourceAt.frame.parameters] using actual
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (decodedArity.symm.trans arity)
  subst decodedSources
  obtain ⟨bodyHeap, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime heapTyped calleeTyped packing packedTyped arity
  have supports := CallableIndexedOwnedPreparedStagedNamedArgumentRows.caller_supports sourceAt wellFormed runtime
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association callStages, SupportFor association callStages packet :=
    fun association => Classical.choice
      (CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.sequence_coverage stagePrepared family
        (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed association)
  let packet := namedTerminals header member
  have children : ∀ {child : Staging.Recursive.Scope}, (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages child callFaults sourceSize := by
    intro child childSelected
    apply CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves
      (namedSupport header member) profile wellFormed childSelected
    intro childSize _smaller childContext childScope current id lowered root
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
      (profile := profile) (closurePackets := fun association => (chosen association).1)
      (closureSupport := fun association => (chosen association).2)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) childSize root
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedNamedApplicationBounds.application_preserves
      functions owner caller header capture sourceAt packet.layouts member wellFormed
      stable bodyHeap argumentsTyped represented heaps supports identity descriptor.id sourceSize children trace (Nat.le_refl _)
  have actualResult : resultCore = header.output := nativeTypes.2.trans header.resultType
  have finalResult := resultAt.2
  rw [← signature.2, ← actualResult] at finalResult
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [nativeEq, packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
  exact ⟨value, finalStore, finalMap, finalWorld, padded.sound, finalResult⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.global function) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
    wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectNamedApplicationBounds
