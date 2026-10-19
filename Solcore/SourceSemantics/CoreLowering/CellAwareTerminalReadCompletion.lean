import Solcore.SourceSemantics.CoreLowering.CellAwareReadMeaningEffects
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion

/-! The actual ordinary-read terminal body completes in a mixed heap.
Its Source trace, native result and descriptor-preserving effect are constructed
from the literal compiler receipts without a body execution hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalReadCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (ResultRepresents control)
open CallableIndexedOwnedAdmittedStagedTerminalBody (terminal_evaluates body_result)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances))
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy} {fuel readFuel : Nat}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {nativeType : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {body : Expr}
  (receipt : Receipt policy fuel invocation.source scope expression statements nativeType reasonAt fellThrough escaped body)
  (read : CompatibleExpressionReads.LoweredRead readFuel (.initial checked)
    invocation.source context reasonAt scope expression receipt.child)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? expression = some node)
  (unique : NodeOccurrencesUnique invocation.source)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {embedding : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world
    administrative scope environment canonical ambient.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
    mapping world before store)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree embedding canonical actual)
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt expression))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
theorem completes :
    ∃ sourceOutcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before
        expression sourceOutcome after ∧
      Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []])
        invocation context environment before statements context
        (control (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f))) after ∧
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults
        (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨certificate, sameChild, binding⟩ := read
  have sameNode := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨childValue, finalStore, evaluated⟩ := certificate.cell_native_terminates functions extension ordinaryCells
    binding environments heaps heapTyped locals agrees
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, preserved, metadata, effect⟩ :=
    certificate.scoped_completed functions extension ordinaryCells program context invocation.evidence binding
      environments heaps heapTyped locals agrees uninitialized evaluated
  obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead certificate.monomorphic
  have staged := CellAwareSelectedReadBounds.staged_of_read (registry := registry)
    certificate unique lookup sourceRead ordinary sourceTrace
  have flow : ∃ flowValue,
      Evaluates actual store ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename embedding)
        flowValue finalStore ∧
      ResultRepresents (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type receipt.child.type faults
        (match outcome with | .value v => .value v | .fault f => .fault (.semantic f)) flowValue := by
    rw [LoopRenaming.returnValue]
    have evaluation : Evaluates actual store (receipt.child.expression.rename embedding) childValue finalStore :=
      evaluated
    simp only [SourceCoreCompatibleValues.Context.initial, sameNode, sameChild] at represented
    cases represented with
    | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluation, .returned payload⟩
    | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluation, .fault (semantic _ _ matched)⟩
  obtain ⟨flowValue, flow, flowRep⟩ := flow
  obtain ⟨value, completed, resultRep⟩ := terminal_evaluates flowRep flow escaped
    (fallback := (CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename embedding)
  refine ⟨outcome, after, value, finalStore, sourceTrace, ?_, ?_, ?_,
    finalHeaps, preserved, metadata, effect⟩
  · cases outcome <;> exact (receipt.head invocation rfl).trace staged
  · rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt embedding]
    exact completed
  · cases outcome <;> simpa only [receipt.sameType] using resultRep

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
/-- Native completion reflects to the independently constructed original body
and exactly the same result, store and retained generalized rows. -/
theorem reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (body.rename embedding) value finalStore) :
    ∃ sourceOutcome : Dynamic.ExpressionOutcome, ∃ after,
      Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []])
        invocation context environment before statements context
        (control (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f))) after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults
        (match sourceOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨sourceOutcome, after, native, reached, _, trace, evaluated, represented, finalHeaps, frame, metadata, effect⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt read found unique
      environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceOutcome, after, trace, represented, finalHeaps, frame, metadata, effect⟩

include extension ordinaryCells read found unique environments heaps heapTyped locals agrees uninitialized semantic in
/-- An independent original terminal trace selects that same complete native
execution. Read uniqueness fixes both the Source result and reached heap. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult node.type bodyOutcome outcome) :
    ∃ value finalStore,
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  have originalRead := read
  obtain ⟨childSize, childOutcome, _, _, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique (receipt.head invocation rfl) trace
  have sameOutcome := CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  obtain ⟨certificate, _sameType, binding⟩ := read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before expression plainOutcome after ∧
      childOutcome = (match plainOutcome with | .value v => .value v | .fault f => .fault (.semantic f)) := by
    cases childOutcome with
    | value value => exact ⟨.value value, .value child.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault child.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (CellAwareSelectedReadBounds.no_stage unique found (nodeEq ▸ certificate.form)
          (nodeEq ▸ certificate.metadata.coercions) child)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨sourceOutcome, actualAfter, value, finalStore, sourceTrace, _, evaluated, represented,
      finalHeaps, frame, metadata, effect⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt originalRead found unique
      environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨location, cell, lookup, sourceRead, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped binding.declared lookup sourceRead certificate.monomorphic
  obtain ⟨rfl, rfl⟩ := CompatibleExpressionReads.source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup sourceRead ordinary sourceTrace plainTrace
  exact ⟨value, finalStore, evaluated, outcomeEq.symm ▸ represented, finalHeaps, frame, metadata, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalReadCompletion
