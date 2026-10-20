import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter

/-! The complete actual materialized body follows its finite compiler tree.
Ordinary allocations extend the heap, map and world while preserving every
captured descriptor and the physical caller frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  (view : View material)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store} {location : Location}
  (entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
    material.origin material.captured material.code inputs functions rawRegistry
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed))
    arguments nativeArguments before store location view.callerNative view.callerGhost view.caller view.id view.recipe)
  {program : Program} (frame : Dynamic.ClosureFrame program function)
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (selected : registry.Closure function invocation)
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (uninitialized : ∀ {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId},
    function.source.lookupExpression? id = some node → node.form = .reference name (.local binder) →
    ∀ location, semanticFaults (.uninitializedLocation location) (material.code.reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "instances" => GeneralizedLocalInstanceValues.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include frame raw in
theorem heap_typed : Dynamic.HeapWellTyped inputs.context entry.entry.heap := by
  have reached := Dynamic.BindersAllocate.preservesHeapTyping raw.heaps raw.arguments entry.entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  exact reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
    frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)


include frame raw selected in
def state : CellAwareLexicalBodyState.Entry functions rawRegistry instances program invocation
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length inputs.context
    (GeneralizedLocalOrdinaryBodyAdmission.scope material) where
  mapping := entry.entry.mapping
  world := entry.entry.world
  administrative := material.captured.administrative
  actualContext := CellAwareParameterTyped.prefixContext material.code.receipt.loweredParameters entry.actualContext
  environment := entry.entry.environment
  canonical := entry.entry.canonical
  actual := entry.entry.actualBody
  heap := entry.entry.heap
  store := entry.entry.store
  embedding := entry.entry.embedding
  location := location
  native := entry.next
  environments := entry.entry.environments
  heaps := entry.entry.heaps
  heapTyped := heap_typed material inputs view functions entry frame raw
  locals := entry.entry.locals
  agrees := entry.entry.lookups
  actualTyped := entry.entry.actualTyped
  reference := entry.entry.reference
  read := entry.entry.read
  unmapped := entry.entry.unmapped
  runtime := by
    have actual := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
    simpa only [registry.source selected] using actual
  covers := by
    have actual := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).2
    simpa only [registry.evidence selected] using actual

structure Result where
  size : Nat
  finalContext : SourceSemantics.Context
  bodyOutcome : Staging.Recursive.BodyOutcome
  outcome : Staging.Recursive.Outcome
  after : Dynamic.Heap
  value : Value
  store : Store
  mapping : LocationMap
  world : StoreTyping
  trace : Staging.Recursive.Size.Statements program registry size invocation inputs.context
    entry.entry.environment entry.entry.heap function.body finalContext bodyOutcome after
  matched : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome
  evaluated : Evaluates entry.entry.actualBody entry.entry.store (material.code.receipt.body.rename entry.entry.embedding) value store
  represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world function.resultType material.code.receipt.resultCore faults outcome value
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  preserved : AdministrativePreserved entry.entry.mapping entry.entry.store mapping store
  effect : CellAwareScopeAuthority.Effect instances entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store mapping world after store
  determines : CellAwareLexicalBodyDeterminacy.Body (program := program) (registry := registry) (invocation := invocation)
    true inputs.context entry.entry.environment entry.entry.heap function.body finalContext bodyOutcome after

include extension frame raw selected selectedBodies uninitialized semantic in
theorem completes : Nonempty (Result (program := program) (registry := registry) (invocation := invocation) (faults := faults) material inputs view functions entry) := by
  obtain ⟨flow,emitted,tree⟩ := GeneralizedLocalOrdinaryBodyAdmission.tree material inputs frame
  have source := registry.source selected
  rw [← source] at tree
  have issued : ∀ context fuel scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked)
        invocation.source context material.code.reasonAt scope id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (material.code.reasonAt id) := by
    intro context fuel scope id lowered receipt
    obtain ⟨leaf,_,_⟩ := receipt
    exact uninitialized (by simpa only [source] using leaf.metadata.found) leaf.form
  let start := state material inputs view functions entry frame raw selected
  obtain ⟨result⟩ := CellAwareLexicalBodyCompletion.completes (registry := registry)
    rfl (CallableIndexedAmbient.frame_registered compiled.indexed) extension issued semantic selectedBodies tree start
  have noEscaped : result.outcome.embed.NoEscapedControl := by
    cases result.outcome <;> constructor <;> intro _ impossible <;> cases impossible
  have represented := result.represented.to_function (GeneralizedLocalOrdinaryBodyAdmission.result_projected material) noEscaped
  obtain ⟨value,evaluated,related⟩ := CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented result.evaluated
    material.code.compilation.internalReason material.code.compilation.internalReason entry.entry.embedding
  exact ⟨{
    size := result.size
    finalContext := result.finalContext
    bodyOutcome := result.outcome.embed
    outcome := CallableIndexedOwnedAdmittedStagedLexicalFlow.result result.outcome.embed
    after := result.after
    value := value
    store := result.store
    mapping := result.mapping
    world := result.world
    trace := result.trace
    matched := result.represented.body_result
    evaluated := by simpa only [emitted,CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename,start,state] using evaluated
    represented := related
    heaps := result.heaps
    preserved := result.preserved
    effect := result.effect
    determines := result.determines }⟩

include extension frame raw selected selectedBodies uninitialized semantic in
theorem preserves {size finalContext bodyOutcome outcome after}
    (trace : Staging.Recursive.Size.Statements program registry size invocation inputs.context
      entry.entry.environment entry.entry.heap function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome) :
    ∃ result : Result (program := program) (registry := registry) (invocation := invocation) (faults := faults) material inputs view functions entry,
      outcome = result.outcome ∧ after = result.after := by
  obtain ⟨result⟩ := completes material inputs view functions extension entry frame raw selected selectedBodies uninitialized semantic
  obtain ⟨_,same,heap⟩ := result.determines trace
  have outcomeEq := (CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched).trans
    ((congrArg CallableIndexedOwnedAdmittedStagedLexicalFlow.result same).trans
      (CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq result.matched).symm)
  exact ⟨result,outcomeEq,heap⟩

include extension frame raw selected selectedBodies uninitialized semantic in
theorem reflects {value finalStore}
    (completed : Evaluates entry.entry.actualBody entry.entry.store
      (material.code.receipt.body.rename entry.entry.embedding) value finalStore) :
    ∃ result : Result (program := program) (registry := registry) (invocation := invocation) (faults := faults) material inputs view functions entry,
      result.value = value ∧ result.store = finalStore := by
  obtain ⟨result⟩ := completes material inputs view functions extension entry frame raw selected selectedBodies uninitialized semantic
  exact ⟨result,evaluation_deterministic result.evaluated completed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyMeaning
