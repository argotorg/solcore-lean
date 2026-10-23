import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryFlow
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt

/-! The actual compiler allocation callback supplies its exact receipts.
The common flow proof keeps compiler request Source and runtime Source distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalControl (absentRequest)
open TypedLexicalWhile (initializedRequest sequence)
variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {stored payload : Ty}
  (reached : index.Reached (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {code : Expr}
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)
  {initializerNode : ExpressionNode} {certificate : GenericExpressionMeaning.Certificate}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificate scope initializer lowered)

include reached read form mono extended allocated childType sourceEq registered bindings initializerFound valueType typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationOrdinaryFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption

include reached read form mono extended allocated childType sourceEq registered bindings initializerFound valueType typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationOrdinaryFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
