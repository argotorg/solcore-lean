import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyReads
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.LexicalBodyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies

/-!
# Generalized locals: body meaning

Meaning of ordinary and terminal bodies and of applications, with Source lifting of an application.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
/-! Original closure typing and actual contextual compilation produce the
whole lexical body tree at the real parameter scope. Every leaf is extracted
from its own accepted callback, including issued reads and numeric literals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  {program : Program} (frame : Dynamic.ClosureFrame program function)

def scope : SourceCoreLocalCell.Scope :=
  material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id,binding.2)) ++ material.inputs.scope

theorem binder_policy : ∀ current binder, binder.scheme.quantified = [] →
    (GeneralizedLocalBodyCompiler.policy material).lowerBinder material.code.view current binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked material.code.view current binder := by
  intro current binder mono
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder,mono,List.isEmpty_nil,↓reduceIte]
  unfold GeneralizedLocalLambdaCompilation.representation
  rw [material.indexed.represented]
  rfl

theorem allocation_policy : (GeneralizedLocalBodyCompiler.policy material).sourceCells =
    some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length (compiled.indexed.layouts.allocatorAt material.code.compilation.owner
        material.code.active material.code.allocationError)) := by
  have accepted := material.code.allocationProfile
  rw [material.policy] at accepted
  exact accepted

theorem result_projected : compiled.compatible.checked.catalog.project function.resultType = .ok material.code.receipt.resultCore := by
  have accepted := material.code.receipt.resultProjected
  simp only [material.policy,material.indexed.projector] at accepted
  exact CompatibleExpressionReads.projectType_of_accepted accepted

include frame in
theorem tree : ∃ flow,
    material.code.receipt.body = CompatibleStatements.finish material.code.receipt.resultCore flow
      material.code.compilation.internalReason material.code.compilation.internalReason ∧
    CellAwareOrdinaryBodyTree.Tree compiled.indexed.layouts material.code.compilation.owner material.code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length material.code.allocationError
      (.initial compiled.compatible.checked) function.source
      (CellAwareLexicalBodyExpressions.StaticCertificate compiled.compatible.checked function.source material.code.reasonAt)
      inputs.context (scope material) true function.body function.resultType material.code.receipt.resultCore flow := by
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have unique : NodeOccurrencesUnique material.code.view := by simpa only [compilerSource] using material.unique
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters
    (values := .initial compiled.compatible.checked) material.code inputs frame material.capturedDeclarations
  obtain ⟨finalContext,facts,bodyTyped,_completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  rw [← compilerSource] at declarations bodyTyped
  have syntaxTree := CellAwareOrdinaryBodySyntax.of_scan (GeneralizedLocalBodyProfileReceipts.scan material)
    unique (GeneralizedLocalBodyProfileReceipts.lexical material) rfl bodyTyped
  have expressions : ∀ sourceContext, ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations material.code.view scope sourceContext →
      GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view id →
      material.code.view.lookupExpression? id = some node → ExpressionHasType material.code.view sourceContext id node.type →
      (GeneralizedLocalBodyCompiler.policy material).lowerExpression fuel material.code.view scope id material.code.reasonAt = .ok lowered →
      CellAwareLexicalBodyExpressions.StaticCertificate compiled.compatible.checked material.code.view material.code.reasonAt sourceContext scope id lowered := by
    intro sourceContext current fuel id node lowered declarations profile found typed accepted
    rw [GeneralizedLocalBodyCompiler.expression_reader] at accepted
    refine ⟨compiled.indexed.fuel,material.code.compilation.solvedRequirements,node,found,typed,?_⟩
    exact GeneralizedLocalBodyExpressionCertificate.of_accepted material profile unique declarations found typed accepted
  have result := CellAwareOrdinaryBodyCollector.tree_of_body (values := .initial compiled.compatible.checked) (GeneralizedLocalBodyCompiler.statement_reader material)
    (binder_policy material) (allocation_policy material) expressions syntaxTree declarations (result_projected material)
    (CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked)
      material.code (GeneralizedLocalBodyCompiler.policy material) (GeneralizedLocalBodyCompiler.callback material))
  simpa only [compilerSource,scope] using result

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyMeaning
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
  have reached := Dynamic.BindersAllocate.preservesHeapTyping (raw.heaps.copy entry.entry.copy)
    (raw.arguments.mono entry.entry.copy.metadata_extends) entry.entry.allocation
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
  actualContext := CellAwareParameterTyped.prefixContext material.code.receipt.loweredParameters entry.entry.copiedContext
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
/-! Independent body execution supplies successful Source admission at the
actual reached heap. The stored compiler's raw return type is retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context staticFinal finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {statements : List StatementId} {type : TypeSystem.Ty} {facts : BodyFacts}
  {size : Nat} {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome}

/-- The genuine Source return rule and selected-registry preservation authenticate
values and deep heap typing. Semantic and staged failures assert no success. -/
theorem successful
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : StatementsHaveType invocation.source {returnType := type} context statements staticFinal facts)
    (completes : BodyCompletes type facts)
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult type bodyOutcome outcome) :
    ∀ value, outcome = .value value →
      Dynamic.ValueHasType context after value type ∧ Dynamic.HeapWellTyped context after := by
  intro value same
  subst outcome
  have preserved := Staging.Recursive.SelectedPreservation.statements selectedBodies
    runtime covers locals heapTyped typed trace
  cases matched with
  | returned => exact ⟨preserved.returned (fun _ => completes) value rfl, preserved.heap_typed⟩
  | unit => exact ⟨.unit, preserved.heap_typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
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
  {registry : Staging.Recursive.Registry}
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
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
    ∃ childSize child copies copied environment bound finalContext bodyOutcome,
      registry.Closure function child ∧
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements program registry childSize child inputs.context environment bound function.body
        finalContext bodyOutcome after ∧ Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _valid extended copy allocated body matched =>
    have same := Dynamic.MonoBindersExtend.functional extended inputs.extended
    subst same
    exact ⟨_, _, _, _, _, _, _, _, selected, copy, allocated, body, matched⟩

include frame raw stable runtime selectedBodies in
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
  have successful := GeneralizedLocalBodySourceAdmission.successful selectedBodies
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

include inputs extension atFrame frame raw stable runtime selectedBodies uninitialized semantic in
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
  obtain ⟨_size, child, copies, copied, environment, bound, finalContext, bodyOutcome, selected, copy, allocated,
      bodyTrace, matched⟩ := source_body material inputs arity trace
  obtain ⟨entry, reached, related, _rows, effect, wrap, _unwrap⟩ :=
    GeneralizedLocalViewedEntry.prepare material view inputs functions owner caller atFrame
      argumentsRep heaps raw.captures stable
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨body,sameOutcome,sameHeap⟩ :=
    GeneralizedLocalOrdinaryBodyMeaning.preserves material inputs view functions extension entry frame raw selected
      selectedBodies uninitialized semantic bodyTrace matched
  refine ⟨body.value, _, wrap body.evaluated, ?_⟩
  exact finish material view inputs functions owner caller frame raw stable runtime selectedBodies
    entry reached related effect selected bodyTrace matched body.effect.maps body.effect.worlds
    (sameOutcome.symm ▸ body.represented) (sameHeap.symm ▸ body.heaps) body.preserved
    (sameHeap.symm ▸ body.effect.metadata) (sameHeap.symm ▸ body.effect)

include inputs extension atFrame frame raw stable runtime selectedBodies uninitialized semantic in
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
      selectedBodies uninitialized semantic bodyEvaluation
  have result := finish material view inputs functions owner caller frame raw stable runtime selectedBodies
    entry reached related effect selected body.trace body.matched body.effect.maps body.effect.worlds
    body.represented body.heaps body.preserved body.effect.metadata body.effect
  refine ⟨_, body.outcome, body.after,
    .closure selected frame inputs.extended entry.entry.copy entry.entry.allocation body.trace body.matched, ?_⟩
  rw [finalEq]
  simpa only [sameValue,sameStore] using result

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
/-! Independent Source calls enter the actual parameter allocation and lift
through the complete finite lexical body extracted from contextual compilation.
Source argument and capture typing refer to the actual incoming heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open Staging.Recursive

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)

include inputs in
/-- The call's copies of the captured cells and the parameter allocation supply
the complete Source state at the body boundary. -/
theorem parameter_state {registry : Registry} {child : Scope}
    (selected : registry.Closure function child)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {arguments : List Dynamic.Value} {before copied bound : Dynamic.Heap} {entry environment : Dynamic.Environment}
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocated : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound) :
    CellAwareOrdinaryBodySourceState.State (program := Program.ofChecked compiled.sourceProgram)
      (invocation := child) inputs.context environment bound := by
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have mono := FunctionCallBody.mono_binders inputs.extended
  have reached := Dynamic.BindersAllocate.preservesHeapTyping (raw.heaps.copy copy)
    (raw.arguments.mono copy.metadata_extends) allocated
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  refine ⟨?_,?_,allocated.preservesEnvironmentAgreement mono.1 mono.2 (copy.agrees raw.captures),?_⟩
  · simpa only [registry.source selected] using runtime.1
  · simpa only [registry.evidence selected] using runtime.2
  · exact reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
      frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)

include inputs in
/-- The original outcome and reached Source heap embed exactly. -/
theorem application_exact {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      registry)
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨childSize, entry, copied, environment, bound, valid, copy, allocated, sourceTrace, _smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨flow,_emitted,tree⟩ := GeneralizedLocalOrdinaryBodyAdmission.tree material inputs valid
  have source := registry.source selected
  rw [← source] at tree
  have plain : SelectedCompilationStageScopedLiftBounds.PlainStatements
      (Program.ofChecked compiled.sourceProgram) true childSize child inputs.context environment bound
      function.body finalContext bodyOutcome after := by
    simpa only [SelectedCompilationStageScopedLiftBounds.PlainStatements, Bool.true_eq, ↓reduceIte, source,registry.evidence selected] using bodyTrace
  obtain ⟨lifted,_post⟩ := CellAwareOrdinaryBodySourceLifting.lifts selectedBodies tree
    (parameter_state material inputs selected valid raw copy allocated) plain
  have matched : BodyResult function.resultType (CellAwareOrdinaryBodySourceState.embed bodyOutcome)
      (Lifting.embed outcome) := by
    cases converted with
    | returned => exact .returned
    | unit _ same => rw [same]; exact .unit
    | fault => exact .fault
    | breaking => exact .breaking
    | continuing => exact .continuing
  exact .closure selected valid inputs.extended copy allocated lifted matched

include inputs in
theorem application {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      registry)
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments outcome after :=
  ⟨_, _, application_exact material inputs selected selectedBodies raw arity trace, .completed⟩

include inputs in
theorem selected_application_exact {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application_exact (registry := SelectedCompilationPhysicalProgramSupport.stages compiled)
    material inputs (.anonymous selected) selectedBodies raw arity trace

include inputs in
/-- The selected child comes from the actual compiler packet retained by the
generalized read, using the public program's complete recursive registry. -/
theorem selected_application {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) caller callContext before
      (.closure function) arguments outcome after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application (registry := SelectedCompilationPhysicalProgramSupport.stages compiled) material inputs (.anonymous selected) selectedBodies raw arity trace

/-- Public representations expose the retained materialization directly; the
actual Source closure frame determines its original parameter context. -/
theorem selected_association_exact
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameter result : Core.Ty}
    (association : Association compiled mapping world function native bindings parameter result)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {caller : Scope} {callContext : SourceSemantics.Context}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  cases association with
  | viewed material _view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    exact selected_application_exact material inputs selectedBodies raw arity trace

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedBodyEntry
/-! A real materialized read enters its stored body using only the input
identities derived from its two actual histories. Captures and the native
frame cell are the same ones retained by the original allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open GeneralizedLocalAcceptedMaterialization
open CallableIndexedLambdaValues CallableIndexedHistory
open SourceCoreCallableIndexedFrames

theorem entry_exists_with_spine
    {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {viewRelation : TypedSource → TypedSource → Prop}
    (material : Materialization compiled mapping world function viewRelation)
    (view : View material)
    (frame : Dynamic.ClosureFrame program function)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry}
    {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      protocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame cells)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world material.code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (read : store.read? view.location =
      some (encode compiled.indexed.ancestry.layout.frame view.transient))
    (unmapped : view.location ∉ mapping)
    (initial : protocol.State ⟨material.inputs.scope, mapping, world, before,
      store.set view.location (encode compiled.indexed.ancestry.layout.frame view.selected),
      material.captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer view.location view.selected) :
    ∃ inputs : CallableIndexedLambdaEntryPrefix.Context
        (values := .initial compiled.compatible.checked) material.code,
      ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked) material.origin material.captured material.code inputs
        functions registry cells arguments nativeArguments before store view.location
        view.callerNative view.callerGhost view.caller view.id view.recipe,
        ∃ added copied : Environment, added.length = material.code.receipt.loweredParameters.length ∧
          entry.entry.canonical = added ++ copied ∧
          (∀ slot, material.inputs.scope.length ≤ slot → copied[slot]? = material.captured.canonical[slot]?) ∧
          ProtectedStateTransition.Transition protocol initial
            ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++
                material.inputs.scope,
              entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  obtain ⟨inputs⟩ := GeneralizedLocalAcceptedBodyCompiler.entry_context material frame material.ownership
  refine ⟨inputs, ?_⟩
  exact GeneralizedLocalBodyEntry.Stateful.entry_exists_with_spine_of_input_ids
    (values := .initial compiled.compatible.checked)
    material.origin material.captured material.code inputs
    (ActualBodyInvocation.materialized_input_ids material view)
    (ActualBodyInvocation.materialized_copied_ids material view)
    functions ordinaryCells protocol producer transport rebinds represented view.carried view.recipe heaps locals
    view.lexicalReference read unmapped initial readyAt

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedBodyEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
/-! Terminal bodies are included in the finite lexical body theorem. These
names retain the earlier entry point while sharing the complete body proof. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
export GeneralizedLocalOrdinaryBodyMeaning (heap_typed preserves reflects)
end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
end
