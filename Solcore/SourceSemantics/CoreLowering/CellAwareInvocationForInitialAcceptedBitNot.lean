import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBitNot
import Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping

/-! Accepted bare bit-not headers use their actual compiler receipt and the
original Source typing to construct the native target before dispatch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty} {assignment : AssignmentResolution}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr}
  (receipt : AcceptedBareBitNotReceipt.Receipt bodyIndex.policy fuel bodyIndex.compilerSource
    scope site assignment (LocalLoop.controlType type) body bodyIndex.reasonAt code)
  (targetType : receipt.binder.scheme.body = assignment.target.type)
  (diagnostic : faults (.semantic (.invalidUnaryOperand .bitNot))
    (receipt.invalidUnary site assignment.target.root))
  {control : ControlContext} {final : SourceSemantics.Context}
  (sourceTyped : ForItemsHaveType invocation.source control context (.assignBitNot assignment :: rest) final)

include transport targetType diagnostic sourceTyped in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements
      expected type code budget := by
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, sourceTyped⟩).1
  rw [receipt.head_emitted targetType typed]
  exact CellAwareInvocationForInitialBitNot.preserves bridge transport functions producer
    (receipt.head targetType typed) typed (receipt.head_errors targetType typed diagnostic) budget tail

include transport targetType diagnostic sourceTyped in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements
      expected type code budget := by
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, sourceTyped⟩).1
  rw [receipt.head_emitted targetType typed]
  exact CellAwareInvocationForInitialBitNot.reflects bridge transport functions producer
    (receipt.head targetType typed) typed (receipt.head_errors targetType typed diagnostic) budget tail

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedBitNot
