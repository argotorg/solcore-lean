import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualLiterals
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence

/-! A finite static fragment for literal/read/group/binary-tuple expressions.
The native code is indexed by the exact compiled child expressions. Product
metadata is related through independent source typing, never native projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Metadata := CompatibleExpressionReads.Metadata

/-- A syntactic restriction on the reached source subtree. It contains no
compiler results, runtime traces, or semantic child hypotheses. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | literal {id node} (found : source.lookupExpression? id = some node)
      (atomic : CompatibleExpressionLiterals.Atomic node.form) : Syntax source id
  | read {id node name binder} (found : source.lookupExpression? id = some node)
      (form : node.form = .reference name (.local binder)) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right])
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

/-- The leaves are the already authenticated literal/read receipts. The
compound rows record independent source type equality and exact child code. -/
inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | literal {id lowered} (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | read {id lowered} (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

private theorem contains_node {source : TypedSource} {id : ExpressionId} {node other : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (contains : ContainsExpression source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

/-- Group raw type equality is recovered from the independent typing rule and
its empty output coercion path. -/
theorem group_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ innerNode, source.lookupExpression? inner = some innerNode ∧ node.type = innerNode.type ∧
      ExpressionHasType source context inner innerNode.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := contains_node unique found contains
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | group child =>
      obtain ⟨innerNode, contained, sameType⟩ := child.stored_type
      exact ⟨innerNode, lookupExpression?_complete unique contained, sameType.symm, sameType ▸ child⟩

/-- Binary tuple source metadata follows `ExpressionsHaveTypes`; no equality
between projected native types is used to identify raw element types. -/
theorem pair_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id left right : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right]) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ leftNode rightNode, source.lookupExpression? left = some leftNode ∧
      source.lookupExpression? right = some rightNode ∧ node.type = .product leftNode.type rightNode.type ∧
      ExpressionHasType source context left leftNode.type ∧ ExpressionHasType source context right rightNode.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := contains_node unique found contains
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawTypeEq : node.type = rawType at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second rest =>
          cases rest
          obtain ⟨leftNode, leftContained, leftType⟩ := first.stored_type
          obtain ⟨rightNode, rightContained, rightType⟩ := second.stored_type
          refine ⟨leftNode, rightNode, lookupExpression?_complete unique leftContained,
            lookupExpression?_complete unique rightContained, ?_, leftType ▸ first, rightType ▸ second⟩
          simp only [TypeSystem.Ty.productMany, ← leftType, ← rightType]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
