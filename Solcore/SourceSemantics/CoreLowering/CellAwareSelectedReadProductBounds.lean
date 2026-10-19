import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedLiteralBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPairBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds

/-! One accepted compiler extraction retains the actual finite literal/read/
group/pair tree and its selected literal sites. Structural recursion constructs
every staged child meaning internally, including ordinary local reads and lazy
mapping initialization at the actual reached state. Source and native grades
remain independent: transparent group reflection uses the same native grade,
while evaluated pair binds use their real strict child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadProductBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareStagedExpressionBounds
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)

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
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) cells)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep}
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    Reaches invocation.source [.expression faultRoot] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension ordinaryCells sameLedger runtimeLedger uninitializedOn semantic unique in
/-- LiteralSites recursion proves each actual Source child internally. A read
uses its genuine local certificate; no read or whole-child meaning is supplied. -/
theorem preserves_reached (size : Nat) :
    PreservesAt bridge context valueModel cells registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CellAwareSelectedLiteralBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique faults size receipt
  | read receipt =>
      intro reached actualNode
      exact CellAwareSelectedReadBounds.preserves_local bridge functions extension ordinaryCells
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel cells registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize innerReached
      intro actualNode
      exact CellAwareStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel cells registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CellAwareSelectedPairBounds.pair_preserves bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension ordinaryCells sameLedger runtimeLedger uninitializedOn semantic unique in
/-- Reflection follows the same finite sites at independent native grades.
Grouping recurses at the same grade; actual pair binds supply strict children. -/
theorem reflects_reached (size : Nat) :
    ReflectsAt bridge context valueModel cells registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CellAwareSelectedLiteralBounds.literal_reflects
        functions bridge sameLedger runtimeLedger faults size receipt
  | read receipt =>
      intro reached actualNode
      exact CellAwareSelectedReadBounds.reflects_local bridge functions extension ordinaryCells
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsAt bridge context valueModel cells registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size innerReached
      intro actualNode
      exact CellAwareStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsBelow bridge context valueModel cells registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CellAwareSelectedPairBounds.pair_reflects bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension ordinaryCells sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context valueModel cells registry invocation trees faults size := by
  intro scope id lowered tree
  exact preserves_reached (faultRoot := id) bridge functions extension ordinaryCells sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

include extension ordinaryCells sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context valueModel cells registry invocation trees faults size := by
  intro scope id lowered tree
  exact reflects_reached (faultRoot := id) bridge functions extension ordinaryCells sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadProductBounds
