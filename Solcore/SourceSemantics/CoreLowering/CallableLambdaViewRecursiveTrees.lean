import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursiveTree

/-! Static source congruence for the recursive constructor/member expression
grammar. Recursion follows every actual child reference, including all lazy
branches, and retains exactly the original code and metadata receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem recursive {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewDataTrees.members edited avoids tree reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

/-- Recover an original recursive tree from the actual compiler view. The same
canonical reachability condition suffices because metadata views retain edges. -/
theorem recursive_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionRecursive.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact recursive reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
