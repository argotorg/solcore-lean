import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree

/-! The original source shape excludes projected unary nodes when an older
uniform diagnostic API requires its original syntax grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedLegacyBranchingTree

theorem GenericForHeader.PreparedSyntax.legacy {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (tree : GenericForHeader.PreparedSyntax source approved context items) (shape : ItemShape items) :
    GenericForHeader.Syntax source approved context items := by
  revert shape
  induction tree with
  | nil => intro _; exact .nil
  | uninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized declaration mono extended ordinary (ih shape.let_tail)
  | initialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized declaration mono extended ordinary found sourceType typed syntaxTree (ih shape.let_tail)
  | discard found typed syntaxTree remaining ih =>
    intro shape
    exact .discard found typed syntaxTree (ih shape.discard_tail)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign sourceTyped writable rightTyped profile children (ih shape.assign_tail.2.2)
  | bitNot writable bare profile remaining ih =>
    intro shape
    exact .bitNot writable bare profile (ih shape.bitNot_tail.2.2)
  | bitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected shape.bitNot_tail.2.1)

theorem GenericImperativeMatch.PreparedSyntax.legacy {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (tree : GenericImperativeMatch.PreparedSyntax source approved context position expected)
    (shape : PositionShape source position) : GenericImperativeMatch.Syntax source approved context position expected := by
  revert shape
  induction tree with
  | body syntaxTree => intro _; exact .body syntaxTree
  | uninitialized found form declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized found form declaration mono extended ordinary (ih (shape.tail_of_let found form))
  | initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree (ih (shape.tail_of_let found form))
  | discard found form notTail sourceType expressionFound typed syntaxTree remaining ih =>
    intro shape
    exact .discard found form notTail sourceType expressionFound typed syntaxTree (ih (shape.discard_tail found form notTail).2)
  | block found form sourceType inner remaining innerIH restIH =>
    intro shape
    exact .block found form sourceType (innerIH (shape.block_children found form).1) (restIH (shape.block_children found form).2)
  | ifThen found form sourceType conditionFound conditionType typed syntaxTree left right remaining leftIH rightIH restIH =>
    intro shape
    exact .ifThen found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2.1) (restIH (shape.branches found form).2.2)
  | breaking found form => intro _; exact .breaking found form
  | continuing found form => intro _; exact .continuing found form
  | whileLoop found form conditionFound conditionType typed syntaxTree inner remaining innerIH restIH =>
    intro shape
    exact .whileLoop found form conditionFound conditionType typed syntaxTree
      (innerIH (shape.loop found form).1) (restIH (shape.loop found form).2)
  | assign found form sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign found form sourceTyped writable rightTyped profile children (ih (shape.assign_tail found form).2.2)
  | forLoop found form sourceType initial remaining initialIH restIH =>
    intro shape
    have parts := shape.for_children found form
    exact .forLoop found form sourceType (initialIH ⟨parts.1, parts.2.1, parts.2.2.1⟩) (restIH parts.2.2.2)
  | initializersDone found sourceType typed syntaxTree loop post ih =>
    intro shape
    exact .initializersDone found sourceType typed syntaxTree (ih shape.2.2) (post.legacy shape.2.1)
  | initializerUninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .initializerUninitialized declaration mono extended ordinary (ih ⟨shape.1.let_tail, shape.2⟩)
  | initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree (ih ⟨shape.1.let_tail, shape.2⟩)
  | initializerDiscard found typed syntaxTree remaining ih =>
    intro shape
    exact .initializerDiscard found typed syntaxTree (ih ⟨shape.1.discard_tail, shape.2⟩)
  | initializerAssign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .initializerAssign sourceTyped writable rightTyped profile children (ih ⟨shape.1.assign_tail.2.2, shape.2⟩)
  | bitNot found form writable bare profile remaining ih =>
    intro shape
    exact .bitNot found form writable bare profile (ih (shape.bitNot_tail found form).2.2)
  | bitNotProjected found form _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.bitNot_tail found form).2.1)
  | initializerBitNot writable bare profile remaining ih =>
    intro shape
    exact .initializerBitNot writable bare profile (ih ⟨shape.1.bitNot_tail.2.2, shape.2⟩)
  | initializerBitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected shape.1.bitNot_tail.2.1)
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children remaining childrenIH restIH =>
    intro shape
    exact .matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid))
      (restIH (shape.match_children found form).2.2)
  | terminalBlock unique found form sourceType inner stops ih =>
    intro shape
    exact .terminalBlock unique found form sourceType (ih (shape.block_children found form).1) stops
  | terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree left right leftStops rightStops leftIH rightIH =>
    intro shape
    exact .terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2.1) leftStops rightStops
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children stops childrenIH =>
    intro shape
    exact .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid)) stops
  | scopedBlock found form inner remaining innerIH restIH =>
    intro shape
    exact .scopedBlock found form (innerIH (shape.block_children found form).1) (restIH (shape.block_children found form).2)

end Solcore.SourceSemantics.CoreLowering
