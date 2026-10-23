import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAllocation
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationHeaderBinders
import Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! The existing absent and initialized header proofs use the same actual
invocation, mixed heap, and concrete allocation request source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open TypedLexicalWhile (initializedRequest sequence)
open TypedLexicalControl (absentRequest)

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
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

variable {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  {parentId : StatementId} {statement : StatementNode}
  {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
  (reached : index.Reached (.statement parentId))
  (found : index.compilerSource.lookupStatement? parentId = some statement)
  (form : statement.form = .forLoop allInitial condition allPost bodyStatements)

section Absent

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  (present : ForItemForm.letDecl binder none ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (projected : projects binder.scheme.body payload)
  (allocated : SourceCoreSourceCells.letUninitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder payload body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_preserves {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.absent_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings projected in
theorem absent_reflects {budget : Nat}
    (ih : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, payload) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type code budget := by
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder none :: rest) expected type
      (.letE annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.absent_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

end Absent

section Initialized

variable {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {binder : TypedBinder} {rest : List ForItemForm} {body code : Expr}
  {expected : TypeSystem.Ty} {type payload : Ty} {administrative : Core.Context}
  {initializer : ExpressionId} {initializerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (present : ForItemForm.letDecl binder (some initializer) ∈ allInitial ++ allPost)
  (binderLowered : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (extended : BinderExtends index.source.owner context binder nextContext)
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (valueType : initializerNode.type = binder.scheme.body)
  (typed : ExpressionHasType index.source context initializer initializerNode.type)
  (certified : certificates context scope initializer lowered)
  (childType : SourceCoreBasic.ensureType (.binder binder.id) payload lowered.type = .ok ())
  (allocated : SourceCoreSourceCells.letInitialized index.policy.sourceCells index.compilerSource scope Renaming.id
    binder (LocalLoop.controlType type) payload lowered.expression body = .ok code)
  (sourceEq : invocation.source = index.source)

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
theorem initialized_preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.initialized_preserves
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

include artifact checked reached found form present binderLowered extended allocated sourceEq registered bindings childType initializerFound valueType typed certified in
theorem initialized_reflects {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (certificates context) faults budget)
    (ih : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge nextContext model index producer registry invocation faults administrative
      ((binder.id, lowered.type) :: scope) rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type code budget := by
  have payloadEq : payload = lowered.type := by
    by_cases sameType : payload = lowered.type
    · exact sameType
    · simp [SourceCoreBasic.ensureType, sameType] at childType
  subst payload
  have mono := index.header_binder_monomorphic artifact checked found form present binderLowered
  obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
  rw [emitted]
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical
  have sourceFound := (index.reached_view.statement (.inr reached)).trans found
  obtain ⟨member, _singleton, ordinary⟩ :=
    SourceLetDeclarationFacts.of_header_lookup physical.ownership sourceFound form present
  have compilerOrdinary := index.compiler_noninput ordinary
  have sound : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context model index producer registry invocation faults administrative
      scope (.letDecl binder (some initializer) :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
    apply CellAwareInvocationForPostAllocation.initialized_reflects
      (allocation := allocation) (annotation := annotation) <;> assumption
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    sourceTyped initial admitted authority physical

end Initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
