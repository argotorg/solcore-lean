import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion

/-! Actual terminal flow branches preserve both Source and native completion
at a named or contextual invocation. Expression semantics are the strict
recursive children, with the same stored descriptors and captured frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {context : SourceSemantics.Context} {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {expected : TypeSystem.Ty}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem preserves {budget : Nat}
    (children : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        certificate faults budget)
    (source : invocation.source = index.source)
    (head : Head invocation expression statements)
    (certified : certificate scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers ledger _sourceTyped initial admitted authority physical
    owner sameLocation _ready finalContext outcome after trace
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameOutcome, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body
      (by simpa only [source] using runtime.graph.nodeOccurrencesUnique) head trace
  subst outcome
  obtain ⟨_trace, value, finalStore, finalMap, finalWorld, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareInvocationTerminalStatements.preserves bridge head certified found typed environments heaps locals
      agrees actualTyped initial admitted authority physical owner sameLocation budget (children runtime covers ledger)
      child (sameSize ▸ within)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
    metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases childOutcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

theorem reflects {budget : Nat}
    (children : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        certificate faults budget)
    (head : Head invocation expression statements)
    (certified : certificate scope expression lowered)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers ledger _sourceTyped initial admitted authority physical
    owner sameLocation _ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, effect, reached, related, post⟩ :=
    CellAwareInvocationTerminalStatements.reflects bridge head certified found typed environments heaps locals agrees
      actualTyped initial admitted authority physical owner sameLocation budget (children runtime covers ledger)
      completed within
  refine ⟨sourceSize, context, CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps,
    worlds, frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | returned payload => exact .returned (valueType ▸ payload)
    | fault matched => exact .fault matched
  · cases outcome <;> simpa only [Post, CallableIndexedOwnedAdmittedStagedTerminalStatements.control, ← valueType] using post

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows
