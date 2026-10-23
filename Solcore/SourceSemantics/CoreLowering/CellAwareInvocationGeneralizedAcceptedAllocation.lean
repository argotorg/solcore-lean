import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt

/-! The actual compiler allocation callback supplies its exact receipts.
The common flow proof keeps compiler request Source and runtime Source distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
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
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  {code : Expr}
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocated childType sourceEq registered bindings in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  have compilerOrdinary := index.compiler_noninput ordinary
  apply CellAwareInvocationGeneralizedFlow.preserves_at_source
    (allocation := allocation) (annotation := annotation) <;> assumption

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocated childType sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  have compilerOrdinary := index.compiler_noninput ordinary
  apply CellAwareInvocationGeneralizedFlow.reflects_at_source
    (allocation := allocation) (annotation := annotation) <;> assumption


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation
