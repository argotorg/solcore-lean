import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectClosureApplications
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins

/-!
# Recursive named public results: direct applications

Bounds of direct application through a handle, for named, builtin, closure, packed and callable values.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedApplicationBounds
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
theorem reflects_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope}
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
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
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
theorem preserves_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope} {tail : Environment}
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
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectNamedApplicationBounds
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
theorem reflects_packed_at_arity [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope}
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
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
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
    apply CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
      (namedSupport header member) profile wellFormed childSelected extension
    · intro childSize _smaller childContext childScope current id lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) rfl childSize root
    · intro childSize _smaller
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects_canonical
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) rfl childSize
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
theorem reflects_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope}
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
theorem preserves_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.global function) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.global function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
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
    apply CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
      (namedSupport header member) profile wellFormed childSelected extension
    · intro childSize _smaller childContext childScope current id lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) childSize root
    · intro childSize _smaller
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves_canonical
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) childSize
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
theorem preserves_value_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope} {tail : Environment}
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectBuiltinApplicationBounds
/-! The authentic builtin identity supplies its ordered parameter row. The
primitive application proof keeps the caller, heap and store unchanged while
relating the actual result to independent Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectBuiltinApplicationBounds
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
  {function : BuiltinFunctionId} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.builtin ⟨function⟩) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function parameter result) (.builtin ⟨function⟩) native
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

include observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Actual complete builtin execution determines the same Source primitive
result and unchanged caller; no builtin body law is supplied by a caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceResult, trace, representedResult, applied, finalStoreEq⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects functions observations builtin rows evaluation
  subst finalStore
  rw [← signature.2, ← nativeTypes.2] at representedResult
  refine ⟨sources, packing, rows.length.1.symm ▸ RecursivePublicCallableArity.Arity.builtin ⟨function⟩, Staging.Recursive.Size.stepSize [], .value sourceResult,
    before, mapping, world, trace, representedResult, heaps, .refl _, .refl _, .refl _ _, .refl _,
    caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity (stagePrepared := stagePrepared) (profile := profile)
      observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed
  exact ⟨sources, packing, meaning⟩

include observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- The actual primitive argument arity fixes its unpacking. Typed primitive
inputs exclude Source dispatch faults; all caller state remains unchanged. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have arity : function.parameterTypes.length = sources.length := arityAt.builtin_count
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (rows.length.1.symm.trans arity)
  subst decodedSources
  obtain ⟨nativeSize, value, evaluated, representedResult, sameHeap, _sourceGrade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions observations builtin rows trace
  subst after
  rw [← signature.2, ← nativeTypes.2] at representedResult
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value store := by
    rw [packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail evaluated
  obtain ⟨source, sameOutcome, _sameHeap, _size, applied⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations rows trace
  cases sameOutcome
  refine ⟨value, store, mapping, world, padded.sound, representedResult, heaps,
    .refl _, .refl _, .refl _ _, .refl _, caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed (stagePrepared := stagePrepared) (profile := profile)
    observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectBuiltinApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableApplicationBounds
/-! Actual Source callable shape selects the existing closure, named or builtin
application proof. The common public input and completion keep the same full
returned caller and independent Source execution for every function kind. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

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
  {function : Dynamic.Value} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before function (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function parameter result) function native
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
/-- The authentic source function branch supplies its actual ordered argument
row; the same native completion reflects independent Source application. -/
theorem reflects_packed_at_arity [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) function sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before function sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  cases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure closure =>
      obtain ⟨sources, packing, arity, reflected⟩ :=
        RecursiveNamedPublicDirectClosureApplicationBounds.reflects_packed
          receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
          wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
      exact ⟨sources, packing, arity.symm ▸ RecursivePublicCallableArity.Arity.closure closure, reflected⟩
  | global global =>
      exact RecursiveNamedPublicDirectNamedApplicationBounds.reflects_packed_at_arity
        receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
        wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  | builtin builtin =>
      cases builtin with
      | mk id =>
        exact RecursiveNamedPublicDirectBuiltinApplicationBounds.reflects_packed_at_arity
          (stagePrepared := stagePrepared) (profile := profile)
          observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
theorem reflects_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before function sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
      wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  exact ⟨sources, packing, meaning⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- An independent Source application at the genuine callable arity preserves
its complete outcome and reached heap. Packing alone does not fix arity. -/
theorem preserves_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) function sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before function sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  cases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure closure =>
      exact RecursiveNamedPublicDirectClosureApplicationBounds.preserves_packed
        receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
        wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
        packing arity.closure_count.symm trace
  | global global =>
      exact RecursiveNamedPublicDirectNamedApplicationBounds.preserves_packed
        receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
        wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
        packing arity trace
  | builtin builtin =>
      cases builtin with
      | mk id =>
        exact RecursiveNamedPublicDirectBuiltinApplicationBounds.preserves_packed
          (stagePrepared := stagePrepared) (profile := profile)
          observations caller stable heapTyped calleeTyped calleeRelated heaps packedRelated packing arity trace

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- Successful Source execution supplies the genuine callable arity. -/
theorem preserves_value_packed [FunctionCalls.FaultTokens semanticFaults] {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before function sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
    wellFormed caller stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableApplicationBounds
end
