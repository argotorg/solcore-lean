import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinTree

/-! Exact builtin expression certificates across local lambda metadata views.
Every recursive child keeps its original raw type, ordered operand code and
contracted callee. Source typing, syntax and compiler acceptance remain separate
static obligations; reachability supplies complete node equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem builtins {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewIndexedTrees.general edited avoids tree reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
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

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (CallableLambdaViewIndexedTrees.header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (firstIH baseReached) (secondIH keyReached)

  | @builtin id callee arguments function node codes identity contract unknown receipt form sourceType count nodes nativeTypes children ih =>
    intro reached
    have childReached : ∀ child, child ∈ arguments → Reaches source roots (.expression child) := by
      intro child member
      exact .expression reached receipt.found (by simp [form, ExpressionForm.references, member])
    exact .builtin (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form sourceType count
      (CallableLambdaViewDataTrees.nodes edited avoids nodes childReached) nativeTypes
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

theorem builtins_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionBuiltins.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact builtins reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
