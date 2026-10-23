import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalFlows

/-! Actual accepted return and tail-expression compiler branches consume the
same smaller expression proof. The child certificate is exactly the policy
call retained by the accepted body tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {context : SourceSemantics.Context} {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep} {administrative : Core.Context}
  {scope : SourceCoreLocalCell.Scope} {id : StatementId} {statement : StatementNode} {stored : Core.Ty}
  {expression : ExpressionId} {node : ExpressionNode} {expected : TypeSystem.Ty}
  {lowered : SourceCoreBasic.LoweredExpr}

def children {bodyRelation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled bodyRelation) (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => index.policy.lowerExpression fuel index.compilerSource scope expression
    index.reasonAt = .ok lowered

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

theorem returning {childFuel budget : Nat} {rest : List StatementId}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .returnStmt (some expression))
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.return_head source rest read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

theorem tail {childFuel budget : Nat}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .expression expression false)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.tail_head source read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
