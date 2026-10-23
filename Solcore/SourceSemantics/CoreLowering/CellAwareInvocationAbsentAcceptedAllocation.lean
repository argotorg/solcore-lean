import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentFlow
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt

/-! The actual compiler allocation callback supplies its exact receipts.
The common flow proof keeps compiler request Source and runtime Source distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
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
  (form : node.form = .letDecl binder none)
  (mono : binder.scheme.quantified = [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {code : Expr}
  (allocated : SourceCoreSourceCells.letUninitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder payload body = .ok code)
  (sourceEq : invocation.source = index.source)
  (projected : projects binder.scheme.body payload)

include reached read form mono extended allocated sourceEq registered bindings projected in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationAbsentFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption

include reached read form mono extended allocated sourceEq registered bindings projected in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, payload) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type code budget := by
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  apply CellAwareInvocationAbsentFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) (allocationInputs := index.compiler_inputs) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
