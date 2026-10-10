import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! A staged user closure invokes its actual retained Code. The original
parameter installation and saved-caller restoration are independent of the
body outcome, so a nested stage failure keeps its Scope/call/tag. A strict
body hypothesis is used only at the real selected parameter entry. Its full
post returns through the saved physical caller; context support follows from
the genuine closure frame and caller runtime validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open Staging.Recursive

private theorem binders_context_eq {owner : Resolved.DeclarationId}
    {before left right : SourceSemantics.Context} {parameters : List TypedBinder}
    {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

/-- The Source application itself selects the genuine staged child Scope and
allocation. Physical arity excludes only the real closureArity alternative. -/
private theorem source_body {program : Program} {stages : Registry}
    {invocation : Scope} {function : Dynamic.Closure} {callContext bodyContext : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {parameterTypes : List TypeSystem.Ty}
    {size : Nat} {outcome : Outcome}
    (parameters : MonoBindersExtend function.source.owner function.context
      function.parameters parameterTypes bodyContext)
    (arity : function.parameters.length = arguments.length)
    (trace : Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) :
    ∃ childSize child environment bound finalContext bodyOutcome,
      stages.Closure function child ∧ Dynamic.ClosureFrame program function ∧
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound ∧
      Size.Statements program stages childSize child bodyContext environment bound function.body
        finalContext bodyOutcome after ∧ BodyResult function.resultType bodyOutcome outcome ∧ childSize < size := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected valid extended allocated body resultRule =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, _, _, _, selected, valid, allocated, body, resultRule,
        Size.child_lt_stepSize (by simp)⟩

section Invocation
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Registry} {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)
  (savedRows : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

/-- A body induction hypothesis at one authentic parameter entry. The final
continuation will construct it from the terminal compiler receipt and strict
expression IH; no body execution law is stored in a static Code receipt. -/
def SourceBodyAt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (bodySize : Nat) : Prop :=
  ∀ {child : Scope} {finalContext : SourceSemantics.Context} {bodyOutcome : BodyOutcome}
    {outcome : Outcome} {after : Dynamic.Heap},
    stages.Closure function child → Dynamic.ClosureFrame program function →
    Size.Statements program stages bodySize child inputs.context entry.entry.environment entry.entry.heap
      function.body finalContext bodyOutcome after → BodyResult function.resultType bodyOutcome outcome →
    ∃ value bodyStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store
        (code.receipt.body.rename entry.entry.embedding) value bodyStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after bodyStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      ∃ bodyState : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, bodyStore, entry.entry.canonical⟩,
        Relates reached bodyState ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context function.resultType outcome bodyState

def ResultAt (outcome : Outcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : State headers keys
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
      Relates caller returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge callerContext function.resultType outcome returned

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The strict staged body is selected by the actual Source closure rule.
Installation, marked parameter allocation and physical caller restoration
are the original producers, each used once at the argument-post pool. -/
theorem invocation_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues nativeArguments ::
        encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, valid, allocated, bodyTrace, resultRule, smaller⟩ := source_body inputs.extended arity trace
  obtain ⟨entry, _added, _length, _spine, parameterState, parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.parameters_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodies entry parameterState childSize (Nat.lt_of_lt_of_le smaller within)
      selected valid bodyTrace resultRule
  obtain ⟨bodyState, bodyRelated, bodyPost⟩ := bodyTransition
  have maps := entry.entry.maps.trans bodyMaps
  have worlds := entry.entry.worlds.trans bodyWorlds
  have frame := entry.entry.frame.trans bodyFrame
  have metadata := entry.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, callerRelated, _records, _returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  have bodyRuntime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters valid inputs.extended).1
  have supports := Dynamic.TypeContextSupports.ofClosed
    (callerRuntime.signatures.trans bodyRuntime.signatures.symm)
    bodyRuntime.closed callerRuntime.closed bodyRuntime.variables_closed callerRuntime.residual_variables_open
  have callerPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows bodyPost supports restoredFrame
  exact ⟨value, _, entry.wrap bodyEvaluation, finalMap, finalWorld, result,
    restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, callerRelated, callerPost⟩


/-- The native body IH is indexed by the actual prefix and reached pool.
Its Source grade is independent of the native child's grade. -/
def NativeBodyAt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (child : Scope) (nativeSize : Nat) : Prop :=
  ∀ {value : Value} {bodyStore : Store},
    EvaluationSize nativeSize entry.actual entry.store
      (code.receipt.body.rename entry.embedding) value bodyStore →
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Size.Statements program stages sourceSize child inputs.context entry.environment entry.heap
        function.body finalContext bodyOutcome after ∧ BodyResult function.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after bodyStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend entry.heap after ∧
      ∃ bodyState : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
        Relates reached bodyState ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context function.resultType outcome bodyState

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The original completion selects its strict native body child. The body
IH reconstructs an independently graded staged Source body, then the literal
closure rule and physical saved-caller restoration run once. -/
theorem invocation_reflects (child : Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function) (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments before store owner.key.frameLocation (caller.rows owner.position).authority.current),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      ∀ childSize, childSize < budget → NativeBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached child childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments ::
        encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Size.Applies program stages sourceSize invocation callContext before (.closure function)
        arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨entry, nativeChild, bodyStore, smaller, bodyCompleted, restored,
    parameterState, parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.body_prefix_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed completed
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
    bodyTrace, resultRule, result, finalHeaps, bodyMaps, bodyWorlds,
    bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodies entry parameterState nativeChild (Nat.lt_of_lt_of_le smaller within) bodyCompleted
  obtain ⟨bodyState, bodyRelated, bodyPost⟩ := bodyTransition
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have metadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, callerRelated, _records, _returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  have bodyRuntime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters valid inputs.extended).1
  have supports := Dynamic.TypeContextSupports.ofClosed
    (callerRuntime.signatures.trans bodyRuntime.signatures.symm)
    bodyRuntime.closed callerRuntime.closed bodyRuntime.variables_closed callerRuntime.residual_variables_open
  have callerPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows bodyPost supports restoredFrame
  subst finalStore
  exact ⟨_, outcome, after, .closure selected valid inputs.extended entry.allocation bodyTrace resultRule,
    finalMap, finalWorld, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, callerRelated, callerPost⟩


include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- Applying the actual retained closure payload preserves the full staged
result. Its one native apply edge encloses the real invocation producer. -/
theorem application_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ :=
    invocation_preserves captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed callerRuntime savedRows budget bodies trace within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The literal payload apply exposes a strict native invocation child.
Its Source closure application is reconstructed with an independent grade. -/
theorem application_reflects (child : Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function) (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments before store owner.key.frameLocation (caller.rows owner.position).authority.current),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      ∀ childSize, childSize < budget → NativeBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached child childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Size.Applies program stages sourceSize invocation callContext before (.closure function)
        arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed callerRuntime savedRows child selected valid budget bodies applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Invocation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
