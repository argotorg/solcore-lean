import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyCompletion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree

/-! Statement shape follows the actual compiler tree, including retained dead
suffixes. It does not assign a result type or a source context to those suffixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedBranchingTree
open CompatibleMatchCertificates GenericMatchChildren SourceCoreCompatibleDataMatches

private theorem original_read {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

/-- Actual header receipts already distinguish bare equal writes. -/
theorem Items.closed_shape {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {finalScope : SourceCoreLocalCell.Scope} {finish : Expr} {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (closed : tree.closed = true) : ItemShape items := by
  induction tree with
  | nil => exact .nil
  | absent _ _ _ ih => exact .absent (ih closed)
  | initialized _ _ _ _ _ _ ih => exact .initialized (ih closed)
  | discard _ _ _ ih => exact .discard (ih closed)
  | assigning | bitNotting => cases closed
  | assigned _ receipt _ ih => exact .assign receipt.sourceProfile receipt.bare (ih closed)
  | projectedAssigned _ receipt _ ih => exact .assignProjected receipt.sourceProfile receipt.projected (ih closed)
  | bitNotted _ receipt _ ih => exact .bitNot receipt.sourceProfile receipt.bare (ih closed)

private theorem arm_shapes {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {id : StatementId} {scope : SourceCoreLocalCell.Scope} {type : TypeSystem.Ty}
    {requests : List Request} {cases : List TypedMatchCase} {native : List (Pattern × Expr)}
    (certificate : Arms compilation source id scope type (Occurs requests) cases native)
    (children : ∀ request ∈ requests, Shape source false request.statements) :
    ∀ arm ∈ cases, Shape source false arm.body := by
  induction certificate with
  | nil => intro arm member; cases member
  | cons pattern typed body tail ih =>
    intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact children _ body
    · exact ih arm member

private theorem match_shapes {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : StatementId}
    {resolution : MatchResolution} {result : Ty} {reason : Word}
    {expressions : ExpressionCertificate} {requests : List Request} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (children : ∀ request ∈ requests, Shape source false request.statements) :
    (∀ arm ∈ resolution.cases, Shape source false arm.body) ∧
    (∀ statements, resolution.defaultBody = some statements → Shape source false statements) := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ arms fallback _ _ =>
    refine ⟨arm_shapes arms children, ?_⟩
    intro statements present
    rw [present] at fallback
    cases fallback with
    | some body => exact children _ body

/-- Each emitted branch and retained suffix supplies its own original shape.
Only the genuine compatible statement reader is needed beyond the formed tree. -/
theorem Tree.formed_shape {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) : Shape source mode statements := by
  induction tree with
  | nil => exact .nil
  | returning read form _ _ _ _ => exact .returnValue _ (original_read (readPolicy ▸ read)) form
  | returnUnit read form _ _ => exact .returnUnit _ (original_read (readPolicy ▸ read)) form
  | breaking read form _ => exact .breaking _ (original_read (readPolicy ▸ read)) form
  | continuing read form _ => exact .continuing _ (original_read (readPolicy ▸ read)) form
  | tailValue read form _ _ _ _ => exact .tail (original_read (readPolicy ▸ read)) form
  | initialized read form _ _ _ _ _ _ _ ih =>
    exact .initialized (original_read (readPolicy ▸ read)) form (ih formed)
  | absent read form _ _ _ _ ih =>
    exact .absent (original_read (readPolicy ▸ read)) form (ih formed)
  | assigned read form _ _ receipt _ ih =>
    exact .assign (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.bare (ih formed)
  | projectedAssigned read form _ _ receipt _ ih =>
    exact .assignProjected (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.projected (ih formed)
  | bitNotted read form _ _ receipt _ ih =>
    exact .bitNot (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.bare (ih formed)
  | discard read form _ _ _ _ ih =>
    exact .discard (original_read (readPolicy ▸ read)) form (.inl rfl) (ih formed)
  | valueDiscard read form _ _ _ _ remaining ih =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .discard (original_read (readPolicy ▸ read)) form (.inr (by simpa using formed.1)) (ih formed.2)
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .block (original_read (readPolicy ▸ read)) form (innerIH formed.1) (tailIH formed.2)
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .conditional (original_read (readPolicy ▸ read)) form
      (leftIH formed.1.1) (rightIH formed.1.2) (tailIH formed.2)
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .whileLoop (original_read (readPolicy ▸ read)) form (innerIH formed.1) (tailIH formed.2)
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have children : ∀ request ∈ receipt.requests, Shape source false request.statements := by
      intro request member
      exact branchIH request member (List.all_eq_true.mp formed.1 ⟨request, member⟩ (by simp))
    obtain ⟨arms, fallback⟩ := match_shapes receipt.certificate children
    exact .matchWith (original_read (readPolicy ▸ read)) form arms fallback (tailIH formed.2)
  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .forLoop (original_read (readPolicy ▸ read)) form
      (initial.closed_shape formed.1.1.1) (after.closed_shape formed.1.2)
      (innerIH formed.1.1.2) (tailIH formed.2)
  | boundary | assigning | bitNotting | forBoundary | matching => cases formed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
