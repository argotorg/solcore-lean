import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadProductBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOperatorBounds

/-! Structural recursion on the accepted expression receipt tree fills every
child of the invocation-family expression heads. Literal and read leaves use
their actual read-product receipts; operator, conditional, group and pair
nodes use their existing heads. No expression meaning is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedExpressionTrees (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension sameLedger uninitialized selectedBodies runtime covers in
/-- Every receipt tree preserves its original staged Source execution at every
Source grade, including failures and the reached mixed-cell heap. -/
theorem preserves_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (tree : trees scope id lowered) (size : Nat) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.preserves bridge functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope inner lowered) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_preserves bridge unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right first second) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_preserves bridge unique (product_values functions) size children
      size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)

include extension sameLedger uninitialized selectedBodies runtime covers in
/-- Every completed native run of a receipt tree reconstructs an independent
Source grade, the same outcome and the reached heap. -/
theorem reflects_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (tree : trees scope id lowered) (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.reflects bridge functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_reflects bridge unique size (ih size)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right first second) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_reflects bridge unique (product_values functions) size children
      size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
