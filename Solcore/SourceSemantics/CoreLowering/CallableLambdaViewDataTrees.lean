import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberTree

/-! Constructor and member certificates across local compiler views. Complete
reached lookups preserve the original instantiation, ordered payload types,
registry header, native layout and generated child code. No new source typing
or compiler acceptance is inferred from this static transport. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
open Core Frontend SourceInference DataPatternValues
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem header {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {tag : ConstructorId} {word : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag word codes) :
    CompatibleExpressionConstructors.Header values view id node instantiation tag word codes :=
  {receipt with metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata}

theorem nodes {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Nodes source ids types codes)
    (reached : ∀ id, id ∈ ids → Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Nodes view ids types codes := by
  induction ids generalizing types codes with
  | nil => cases receipt; exact .nil
  | cons id ids ih =>
    cases types with
    | nil => cases receipt; exact .nil
    | cons type types =>
      cases receipt with
      | cons head tail =>
        obtain ⟨node, found, rawType⟩ := head
        exact .cons ⟨node, (expression_lookup edited avoids (reached id (by simp))).symm.trans found, rawType⟩
          (ih tail (fun child member => reached child (by simp [member])))

omit edited avoids in
theorem constructor_children {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    (reached : Reaches source roots (.expression id)) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation ids) :
    ∀ child, child ∈ ids → Reaches source roots (.expression child) := by
  intro child member
  exact .expression reached found (by simp [form, ExpressionForm.references, member])

theorem constructors {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewScalarTrees.conditionals edited avoids tree reached)
  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := constructor_children reached receipt.metadata.found form
    exact .constructor (header edited avoids reached receipt) form valid count
      (nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

theorem members {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionMembers.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (constructors edited avoids tree reached)
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
