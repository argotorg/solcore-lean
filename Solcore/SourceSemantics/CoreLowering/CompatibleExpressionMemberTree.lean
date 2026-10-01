import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberSource

/-! Finite member chains over the already certified constructor expression
fragment. Every child certificate is structural; no execution is stored. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionReads

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionConstructors.Syntax source id) : Syntax source id
  | member {id node base name index} (found : source.lookupExpression? id = some node)
      (form : node.form = .member base name index) (child : Syntax source base) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child) :
      Tree fuel values source context solved reasonAt scope id
        ⟨result, SourceCoreDataExpressions.member identity result branches child.expression⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
