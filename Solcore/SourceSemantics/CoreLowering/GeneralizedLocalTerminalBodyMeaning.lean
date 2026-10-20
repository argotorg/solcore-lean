import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects
import Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! Actual generalized lambda compilation and marked parameter allocation
supply the terminal read body correspondence. No body execution law or child
certificate is accepted from a caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
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
  (wellFormed : ProgramWellFormed program)
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

include extension frame raw selected wellFormed uninitialized semantic in
/-- Preservation follows the same terminal body and genuine parameter heap.
The returned map and world are those already allocated by the real prefix. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation inputs.context
      entry.entry.environment entry.entry.heap function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome) :
    ∃ value finalStore,
      Evaluates entry.entry.actualBody entry.entry.store
        (material.code.receipt.body.rename entry.entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model entry.entry.mapping entry.entry.world
        function.resultType material.code.receipt.resultCore faults outcome value ∧
      GenericHeap.CellHeapRepresents cells entry.entry.mapping entry.entry.world after finalStore ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store entry.entry.mapping finalStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      CellAwareScopeAuthority.Effect instances entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store
        entry.entry.mapping entry.entry.world after finalStore := by
  obtain ⟨receipt⟩ := GeneralizedLocalBodyProfileReceipts.receipt material
  have source := registry.source selected
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  obtain ⟨read, resultType, typed⟩ := GeneralizedLocalBodyExpressionAdmission.actual_tree material inputs frame source receipt
  let terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt
      (GeneralizedLocalBodyCompiler.policy material) material.code.fuel invocation.source
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      material.bodyProfile.expression function.body material.code.receipt.resultCore material.code.reasonAt
      material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body := {
    childFuel := receipt.childFuel
    child := receipt.child
    predecessor := receipt.predecessor
    generated := by simpa only [source, ← compilerSource] using receipt.generated
    sameType := receipt.sameType
    terminal := by simpa only [source, ← compilerSource] using receipt.terminal
    accepted := by simpa only [source, ← compilerSource] using receipt.accepted
    emitted := receipt.emitted }
  simp only [← source, compilerSource] at read typed
  let site := GeneralizedLocalBodyProfileReceipts.expression_site material
  have siteType : site.node.type = function.resultType := resultType
  have found := site.found
  simp only [compilerSource, ← source] at found
  have unique : NodeOccurrencesUnique invocation.source := by simpa only [source] using material.unique
  have runtimeAt := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have runtime : Dynamic.SourceRuntimeValid program inputs.context invocation.source := by
    simpa only [source] using runtimeAt.1
  have covers : invocation.evidence.Covers inputs.context := by
    simpa only [registry.evidence selected] using runtimeAt.2
  have issued : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
        invocation.source inputs.context material.code.reasonAt scope id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (material.code.reasonAt id) := by
    intro scope id lowered receipt
    obtain ⟨leaf, _, _⟩ := receipt
    exact uninitialized (by simpa only [source] using leaf.metadata.found) leaf.form
  have result := CellAwareTerminalExpressionCompletion.preserves (program := program) (registry := registry) (outcome := outcome) functions extension
    GeneralizedLocalDescriptorHeap.ordinary_cells terminal read found unique typed wellFormed runtime covers
    entry.entry.environments entry.entry.heaps (heap_typed material inputs view functions entry frame raw)
    entry.entry.locals entry.entry.lookups issued semantic trace
    (by simpa only [siteType] using matched)
  simp only [siteType] at result
  exact result

include extension frame raw selected wellFormed uninitialized semantic in
/-- Native body completion reconstructs the independently graded Source body
using its actual compilation and parameter initialization receipts. -/
theorem reflects {value : Value} {finalStore : Store}
    (completed : Evaluates entry.entry.actualBody entry.entry.store
      (material.code.receipt.body.rename entry.entry.embedding) value finalStore) :
    ∃ sourceSize, ∃ sourceOutcome : Dynamic.ExpressionOutcome, ∃ after,
      Staging.Recursive.Size.Statements program registry sourceSize invocation inputs.context
        entry.entry.environment entry.entry.heap function.body inputs.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control
          (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f))) after ∧
      RecursiveStageMeaning.ResultRepresentsFor model entry.entry.mapping entry.entry.world
        function.resultType material.code.receipt.resultCore faults
        (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) value ∧
      GenericHeap.CellHeapRepresents cells entry.entry.mapping entry.entry.world after finalStore ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store entry.entry.mapping finalStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      CellAwareScopeAuthority.Effect instances entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store
        entry.entry.mapping entry.entry.world after finalStore := by
  obtain ⟨receipt⟩ := GeneralizedLocalBodyProfileReceipts.receipt material
  have source := registry.source selected
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  obtain ⟨read, resultType, typed⟩ := GeneralizedLocalBodyExpressionAdmission.actual_tree material inputs frame source receipt
  let terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt
      (GeneralizedLocalBodyCompiler.policy material) material.code.fuel invocation.source
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      material.bodyProfile.expression function.body material.code.receipt.resultCore material.code.reasonAt
      material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body := {
    childFuel := receipt.childFuel
    child := receipt.child
    predecessor := receipt.predecessor
    generated := by simpa only [source, ← compilerSource] using receipt.generated
    sameType := receipt.sameType
    terminal := by simpa only [source, ← compilerSource] using receipt.terminal
    accepted := by simpa only [source, ← compilerSource] using receipt.accepted
    emitted := receipt.emitted }
  simp only [← source, compilerSource] at read typed
  let site := GeneralizedLocalBodyProfileReceipts.expression_site material
  have siteType : site.node.type = function.resultType := resultType
  have found := site.found
  simp only [compilerSource, ← source] at found
  have unique : NodeOccurrencesUnique invocation.source := by simpa only [source] using material.unique
  have runtimeAt := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have runtime : Dynamic.SourceRuntimeValid program inputs.context invocation.source := by
    simpa only [source] using runtimeAt.1
  have covers : invocation.evidence.Covers inputs.context := by
    simpa only [registry.evidence selected] using runtimeAt.2
  have issued : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
        invocation.source inputs.context material.code.reasonAt scope id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (material.code.reasonAt id) := by
    intro scope id lowered receipt
    obtain ⟨leaf, _, _⟩ := receipt
    exact uninitialized (by simpa only [source] using leaf.metadata.found) leaf.form
  have result := CellAwareTerminalExpressionCompletion.reflects (program := program) (registry := registry) functions extension
    GeneralizedLocalDescriptorHeap.ordinary_cells terminal read found unique typed wellFormed runtime covers
    entry.entry.environments entry.entry.heaps (heap_typed material inputs view functions entry frame raw)
    entry.entry.locals entry.entry.lookups issued semantic completed
  simp only [siteType] at result
  exact result

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
