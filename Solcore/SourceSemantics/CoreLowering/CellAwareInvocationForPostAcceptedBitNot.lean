import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBitNot
import Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping

/-! Accepted bare bit-not headers use their actual compiler receipt and the
original Source typing to construct the native target before dispatch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedBitNot
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
  (sourceEq : invocation.source = bodyIndex.source)

include transport targetType diagnostic sourceEq in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
  obtain ⟨control, final, original⟩ := sourceTyped
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩).1
  have assignmentTyped := sourceEq.symm ▸ typed
  have sound := CellAwareInvocationForPostBitNot.preserves bridge transport functions producer
    (receipt.head targetType assignmentTyped) sourceEq
    (receipt.head_errors targetType assignmentTyped diagnostic) budget tail
  rw [← receipt.head_emitted targetType assignmentTyped] at sound
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    ⟨control, final, original⟩

include transport targetType diagnostic sourceEq in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
  obtain ⟨control, final, original⟩ := sourceTyped
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩).1
  have assignmentTyped := sourceEq.symm ▸ typed
  have sound := CellAwareInvocationForPostBitNot.reflects bridge transport functions producer
    (receipt.head targetType assignmentTyped) sourceEq
    (receipt.head_errors targetType assignmentTyped diagnostic) budget tail
  rw [← receipt.head_emitted targetType assignmentTyped] at sound
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    ⟨control, final, original⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedBitNot
