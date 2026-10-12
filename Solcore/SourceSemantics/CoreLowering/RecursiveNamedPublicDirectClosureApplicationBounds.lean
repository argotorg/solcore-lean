import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult

/-! Direct packed application reuses the established numeric body family.
The retained callable, current captures and owned caller state supply the
application boundary; no body execution law is an input. -/
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


/-- The host's ambient environment is not read by the literal application.
The same body evaluation and exact native size are retained. -/
theorem application_tail {size : Nat} {callable packed value : Value}
    {tail other : Environment} {store finalStore : Store}
    (completed : EvaluationSize size (callable :: packed :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    EvaluationSize size (callable :: packed :: other) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
  cases completed with
  | apply callee argument body =>
    cases callee with
    | second first =>
      cases first with
      | first selected =>
        cases selected with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst callable
          cases argument with
          | var found =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
            subst packed
            exact .apply (.second (.first (.var rfl))) (.var rfl) body

section Closure
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
  {function : Dynamic.Closure} {native : Value} {result : TypeSystem.Ty} {resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function .unit result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function .unit result) (.closure function) native
    (CallableContract.functionType .unit resultCore))
  (parameters : function.parameters = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated parameters heaps in
/-- A retained zero-parameter closure reflects its actual packed Unit call.
Static body coverage closes every recursive child through the existing numeric family. -/
theorem reflects_unit {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: .unit :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
        invocation context before (.closure function) [] outcome after ∧
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
  obtain ⟨bindings, parameterCore, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have bindingsNil : bindings = [] := by
    have sourceBinders := association.source_binders
    rw [parameters, List.map_nil] at sourceBinders
    exact List.map_eq_nil_iff.mp sourceBinders
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      mapping world bindings [] [] := by
    rw [bindingsNil]
    exact .nil
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    (arguments := []) (types := []) (.nil) (.nil) rfl (by simp [parameters])
  obtain ⟨_parameter, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues []] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := application_tail completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds.application_reflects
      profile association (chosen association).1 (chosen association).2 caller raw represented heaps stable runtime
      valid size (fun childSize _ => bodies childSize) (fun childSize _ => canonicalBodies childSize) evaluation (Nat.le_refl _)
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
end Closure
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
