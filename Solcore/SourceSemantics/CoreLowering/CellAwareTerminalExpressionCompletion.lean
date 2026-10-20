import Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion

/-! The actual ordinary expression terminal body completes in a mixed heap.
Its Source trace, native result and descriptor-preserving effect are constructed
from the literal compiler receipts without a body execution hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
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
  {solved : List SolvedRequirement}
  (certificate : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel (.initial checked)
    invocation.source context solved reasonAt scope expression receipt.child)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? expression = some node)
  (unique : NodeOccurrencesUnique invocation.source)
  (typed : ExpressionHasType invocation.source context expression node.type)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
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
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
theorem completes :
    ∃ size sourceOutcome after value finalStore,
      Staging.Recursive.Size.Statements program registry size invocation context environment before statements context
        (control (Staging.Recursive.Lifting.embed sourceOutcome)) after ∧
      Evaluates actual store (body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults (Staging.Recursive.Lifting.embed sourceOutcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context environment before expression otherOutcome otherHeap →
        otherOutcome = Staging.Recursive.Lifting.embed sourceOutcome ∧ otherHeap = after := by
  obtain ⟨size, outcome, after, childValue, finalStore, staged, evaluated, represented,
      finalHeaps, preserved, metadata, effect, determines⟩ :=
    CellAwareReadProductCompletion.completes functions extension ordinaryCells uninitialized semantic unique
      wellFormed runtime covers certificate found typed environments heaps heapTyped locals agrees
  have flow : ∃ flowValue,
      Evaluates actual store ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename embedding)
        flowValue finalStore ∧
      ResultRepresents (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type receipt.child.type faults (Staging.Recursive.Lifting.embed outcome) flowValue := by
    rw [LoopRenaming.returnValue]
    cases outcome with
    | value value =>
      cases represented with
      | value payload => exact ⟨_, LocalLoop.returnValue_success _ evaluated, .returned payload⟩
    | fault reason =>
      cases represented with
      | fault matched => exact ⟨_, LocalLoop.returnValue_failure _ evaluated, .fault matched⟩
  obtain ⟨flowValue, flow, flowRep⟩ := flow
  obtain ⟨value, completed, resultRep⟩ := terminal_evaluates flowRep flow escaped
    (fallback := (CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename embedding)
  refine ⟨_, outcome, after, value, finalStore, (receipt.head invocation rfl).trace staged, ?_, ?_,
    finalHeaps, preserved, metadata, effect, determines⟩
  · rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt embedding]
    exact completed
  · simpa only [receipt.sameType] using resultRep

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
theorem reflects {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (body.rename embedding) value finalStore) :
    ∃ size sourceOutcome after,
      Staging.Recursive.Size.Statements program registry size invocation context environment before statements context
        (control (Staging.Recursive.Lifting.embed sourceOutcome)) after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
        mapping world node.type nativeType faults (Staging.Recursive.Lifting.embed sourceOutcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) instances)
        mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store mapping world after finalStore := by
  obtain ⟨size, sourceOutcome, after, native, reached, trace, evaluated, represented, finalHeaps, frame, metadata, effect, _⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt certificate found unique
      typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨size, sourceOutcome, after, trace, represented, finalHeaps, frame, metadata, effect⟩

include extension ordinaryCells certificate found unique typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic in
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
  obtain ⟨childSize, childOutcome, _, _, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique (receipt.head invocation rfl) trace
  have sameOutcome := CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  obtain ⟨_, sourceOutcome, actualAfter, value, finalStore, _, evaluated, represented,
      finalHeaps, frame, metadata, effect, determines⟩ :=
    completes (program := program) (registry := registry) functions extension ordinaryCells receipt certificate found unique
      typed wellFormed runtime covers environments heaps heapTyped locals agrees uninitialized semantic
  obtain ⟨rfl,rfl⟩ := determines child
  exact ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalExpressionCompletion
