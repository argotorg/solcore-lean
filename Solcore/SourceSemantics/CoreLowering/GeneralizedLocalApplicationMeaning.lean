import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission

/-! Actual generalized local application joins the original Source rule,
marked parameters, certified terminal body, and saved physical caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open GeneralizedLocalMaterializedAssociation
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  (material : Materialization compiled mapping world function) (view : View material)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (atFrame : view.location = owner.key.frameLocation)
  (frame : Dynamic.ClosureFrame program function)
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
  (stable : StableRows caller)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid program callerContext callerSource)
  (wellFormed : ProgramWellFormed program)
  {registry : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId},
    function.source.lookupExpression? id = some node → node.form = .reference name (.local binder) →
    ∀ location, semanticFaults (.uninitializedLocation location) (material.code.reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "instances" => GeneralizedLocalInstanceValues.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge

/-- All outputs refer to one actual caller restoration. -/
def ResultAt (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld function.resultType material.code.receipt.resultCore faults outcome value ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
    ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      Relates caller returned ∧ PostAdmission bridge callerContext function.resultType outcome returned

private theorem source_body {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context}
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (arity : function.parameters.length = arguments.length)
    (trace : Staging.Recursive.Size.Applies program registry size invocation callContext before
      (.closure function) arguments outcome after) :
    ∃ childSize child environment bound finalContext bodyOutcome,
      registry.Closure function child ∧
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements program registry childSize child inputs.context environment bound function.body
        finalContext bodyOutcome after ∧ Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _valid extended allocated body matched =>
    have same := Dynamic.MonoBindersExtend.functional extended inputs.extended
    subst same
    exact ⟨_, _, _, _, _, _, selected, allocated, body, matched⟩

include frame raw stable runtime wellFormed in
/-- Concrete body completion and actual Source execution restore the original
caller, every reached owned record, and both kinds of represented Source cells. -/
theorem finish
    (entry : GeneralizedLocalViewedEntry.Entry (registry := rawRegistry) (arguments := arguments)
      (nativeArguments := nativeArguments) (before := before) (store := store) material view inputs functions owner)
    (reached : State headers keys
      ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (related : Relates caller reached)
    (prefixEffect : CellAwareScopeAuthority.Effect instances mapping world before store
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store)
    {child : Staging.Recursive.Scope} (selected : registry.Closure function child)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {value : Value} {bodyStore : Store}
    (trace : Staging.Recursive.Size.Statements program registry size child inputs.context
      entry.entry.environment entry.entry.heap function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome)
    {bodyMap : LocationMap} {bodyWorld : StoreTyping}
    (bodyMaps : LocationMap.Extends entry.entry.mapping bodyMap)
    (bodyWorlds : WorldExtends entry.entry.world bodyWorld)
    (represented : RecursiveStageMeaning.ResultRepresentsFor model bodyMap bodyWorld
      function.resultType material.code.receipt.resultCore faults outcome value)
    (heaps : GenericHeap.CellHeapRepresents cells bodyMap bodyWorld after bodyStore)
    (bodyFrame : AdministrativePreserved entry.entry.mapping entry.entry.store bodyMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend entry.entry.heap after)
    (effect : CellAwareScopeAuthority.Effect instances entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store
      bodyMap bodyWorld after bodyStore) :
    ResultAt (rawRegistry := rawRegistry) (faults := faults) (callerContext := callerContext) material functions caller outcome after value
      (bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  let bodyState := (administrativeTransport headers keys).extend reached
    bodyMaps bodyWorlds bodyFrame metadata
  have bodyRelated : Relates reached bodyState := Relates.of_records_eq rfl
  have bodyCaller := related.trans bodyRelated
  have prefixFrame : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame entry.next))
      entry.entry.mapping entry.entry.store := by
    have prefixPreserved := entry.entry.frame
    simp only [List.set_set] at prefixPreserved
    exact prefixPreserved
  have fullFrame := prefixFrame.trans bodyFrame
  obtain ⟨finalHeaps, finalFrame, _current, finalRelated⟩ := CellAwareOwnedBodyRestoration.restore_return
    caller bodyState owner.position heaps (entry.entry.worlds.trans bodyWorlds) fullFrame bodyCaller
  have finalEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances
    (prefixEffect.trans effect)
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have rows : StableRows returned := StableRows.after_administrative caller returned stable finalFrame
  have bodyRuntime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have supports := Dynamic.TypeContextSupports.ofClosed
    (runtime.signatures.trans bodyRuntime.1.signatures.symm) bodyRuntime.1.closed runtime.closed
    bodyRuntime.1.variables_closed runtime.residual_variables_open
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  have source := registry.source selected
  have evidence := registry.evidence selected
  have typedAt : StatementsHaveType child.source {returnType := function.resultType} inputs.context
      function.body staticFinal facts := by simpa only [source] using bodyTyped
  have successful := GeneralizedLocalBodySourceAdmission.successful wellFormed
    (by simpa only [source] using bodyRuntime.1) (by simpa only [evidence] using bodyRuntime.2)
    entry.entry.locals (GeneralizedLocalOrdinaryBodyMeaning.heap_typed material inputs view functions entry frame raw)
    typedAt completes trace matched
  have post : PostAdmission bridge callerContext function.resultType outcome returned := by
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      obtain ⟨valueTyped, heapTyped⟩ := successful sourceValue rfl
      exact ⟨valueTyped.transportContext supports, heapTyped.transportContext supports⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨rows, by intro value same; cases same⟩
      | stage _ _ _ => exact rows
  exact ⟨bodyMap, bodyWorld, represented, finalHeaps, entry.entry.maps.trans bodyMaps,
    entry.entry.worlds.trans bodyWorlds, finalFrame, entry.entry.metadata.trans metadata, finalEffect, returned, finalRelated, post⟩

include inputs extension atFrame frame raw stable runtime wellFormed uninitialized semantic in
/-- Source application selects the actual body and parameter allocation. The
native call is assembled from the concrete outer wrapper and terminal body. -/
theorem preserves
    (argumentsRep : CallableIndexedParameterMeaning.Arguments model mapping world
      material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context}
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies program registry size invocation callContext before
      (.closure function) arguments outcome after) :
    ∃ value finalStore,
      Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (rawRegistry := rawRegistry) (faults := faults) (callerContext := callerContext) material functions caller outcome after value finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) material.code, List.length_map]
    exact argumentsRep.length.1
  obtain ⟨_size, child, environment, bound, finalContext, bodyOutcome, selected, allocated, bodyTrace, matched⟩ :=
    source_body material inputs arity trace
  obtain ⟨entry, reached, related, _rows, effect, wrap, _unwrap⟩ :=
    GeneralizedLocalViewedEntry.prepare material view inputs functions owner caller atFrame
      argumentsRep heaps raw.captures stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨body,sameOutcome,sameHeap⟩ :=
    GeneralizedLocalOrdinaryBodyMeaning.preserves material inputs view functions extension entry frame raw selected
      wellFormed uninitialized semantic bodyTrace matched
  refine ⟨body.value, _, wrap body.evaluated, ?_⟩
  exact finish material view inputs functions owner caller frame raw stable runtime wellFormed
    entry reached related effect selected bodyTrace matched body.effect.maps body.effect.worlds
    (sameOutcome.symm ▸ body.represented) (sameHeap.symm ▸ body.heaps) body.preserved
    (sameHeap.symm ▸ body.effect.metadata) (sameHeap.symm ▸ body.effect)

include inputs extension atFrame frame raw stable runtime wellFormed uninitialized semantic in
/-- Native completion reflects through the same authentic view and parameters,
returning its independent Source grade and the exact restored caller state. -/
theorem reflects
    (argumentsRep : CallableIndexedParameterMeaning.Arguments model mapping world
      material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {child : Staging.Recursive.Scope} (selected : registry.Closure function child)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {value : Value} {finalStore : Store}
    (completed : Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ size outcome after,
      Staging.Recursive.Size.Applies program registry size invocation callContext before
        (.closure function) arguments outcome after ∧
      ResultAt (rawRegistry := rawRegistry) (faults := faults) (callerContext := callerContext) material functions caller outcome after value finalStore := by
  obtain ⟨entry, reached, related, _rows, effect, _wrap, unwrap⟩ :=
    GeneralizedLocalViewedEntry.prepare material view inputs functions owner caller atFrame
      argumentsRep heaps raw.captures stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  obtain ⟨body,sameValue,sameStore⟩ :=
    GeneralizedLocalOrdinaryBodyMeaning.reflects material inputs view functions extension entry frame raw selected
      wellFormed uninitialized semantic bodyEvaluation
  have result := finish material view inputs functions owner caller frame raw stable runtime wellFormed
    entry reached related effect selected body.trace body.matched body.effect.maps body.effect.worlds
    body.represented body.heaps body.preserved body.effect.metadata body.effect
  refine ⟨_, body.outcome, body.after, .closure selected frame inputs.extended entry.entry.allocation body.trace body.matched, ?_⟩
  rw [finalEq]
  simpa only [sameValue,sameStore] using result

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
