import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedTree

/-! Mapping index and typed recursive trees across local compiler views.
The exact prepared comparator, default-producing reads, raw key/result types
and actual child code are retained. Reachability constrains edits; typing and
accepted compiler equations remain independent static obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem header {id base : ExpressionId} {node baseNode : ExpressionNode}
    {layout : OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id)) (baseReached : Reaches source roots (.expression base))
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second) :
    CompatibleExpressionIndices.Header values view id base node baseNode layout comparison first second :=
  {receipt with metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata
                baseMetadata := CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached receipt.baseMetadata}

theorem indices {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionIndices.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionIndices.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewDataTrees.members edited avoids tree reached)
  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType scalar (firstIH baseReached) (secondIH keyReached)

theorem typed {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionTyped.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached)
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

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType scalar (firstIH baseReached) (secondIH keyReached)

theorem general {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached)
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
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (firstIH baseReached) (secondIH keyReached)

theorem indices_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionIndices.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionIndices.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact indices reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

theorem typed_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionTyped.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact typed reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

theorem general_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionGeneral.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact general reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
