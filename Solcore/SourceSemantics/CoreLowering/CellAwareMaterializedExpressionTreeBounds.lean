import Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPairBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedReadProjection

/-! Structural recursion on the genuine named compiler tree fills every child
expression. Generalized reads and products retain positive materialized leaves; no whole-expression meaning is stored in a certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareMaterializedScopeBounds
open CallableIndexedNamedGeneration (Compilation)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareMaterializedExpressionCertificates (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values : CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique in
theorem preserves_tree
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    PreservesAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareMaterializedReadProjection.preserves bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation (Point scope inner lowered) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareMaterializedGroupBounds.group_preserves bridge unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareMaterializedPairBounds.pair_preserves bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
