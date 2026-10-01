import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductCertificates

/-! Primitive trees contain static metadata and operator profiles only.
Product fragments retain their existing actual compiler certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | product {id} (child : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right]) (first : Syntax source left) (second : Syntax source right) : Syntax source id
  | unary {id node operand operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : Syntax source operand) : Syntax source id
  | binary {id node left right operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right)
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | product {id lowered}
      (child : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : Tree fuel values source context solved reasonAt scope operand ⟨core.operandType, childCode⟩) :
      Tree fuel values source context solved reasonAt scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : Tree fuel values source context solved reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree fuel values source context solved reasonAt scope right ⟨mode.operandType operator, rightCode⟩) :
      Tree fuel values source context solved reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

private theorem contains_node {source : TypedSource} {id : ExpressionId} {node other : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (contains : ContainsExpression source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

theorem unary_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id operand : ExpressionId} {node : ExpressionNode} {operator : Syntax.UnaryOp}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .unary operator operand) (coercions : node.coercions = [])
    (requirements : node.requirements = []) (typed : ExpressionHasType source context id node.type) :
    ∃ childNode core, source.lookupExpression? operand = some childNode ∧
      ExpressionHasType source context operand childNode.type ∧ UnaryProfile operator childNode.type node.type core := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := contains_node unique found contains
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw valid
    cases raw with
    | unary child operatorTyped =>
      cases valid with
      | ordinary _ _ layout =>
        rw [requirements, coercions] at layout
        simp only [coercionRequirementIds, List.flatMap_nil, List.append_nil] at layout
        rw [← layout] at operatorTyped
        obtain ⟨childNode, contains, typeEq⟩ := child.stored_type
        obtain ⟨core, profile⟩ := UnaryProfile.of_typing operatorTyped
        exact ⟨childNode, core, lookupExpression?_complete unique contains, typeEq ▸ child, typeEq ▸ (resultEq ▸ profile)⟩

theorem binary_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id left right : ExpressionId} {node : ExpressionNode} {operator : Syntax.BinaryOp}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .binary left operator right) (coercions : node.coercions = [])
    (requirements : node.requirements = []) (typed : ExpressionHasType source context id node.type) :
    ∃ leftNode rightNode mode, source.lookupExpression? left = some leftNode ∧
      source.lookupExpression? right = some rightNode ∧ leftNode.type = rightNode.type ∧
      ExpressionHasType source context left leftNode.type ∧ ExpressionHasType source context right rightNode.type ∧
      BinaryProfile operator leftNode.type node.type mode := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := contains_node unique found contains
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw valid
    cases raw with
    | binary first second operatorTyped =>
      cases valid with
      | ordinary _ _ layout =>
        rw [requirements, coercions] at layout
        simp only [coercionRequirementIds, List.flatMap_nil, List.append_nil] at layout
        rw [← layout] at operatorTyped
        obtain ⟨leftNode, leftContains, leftType⟩ := first.stored_type
        obtain ⟨rightNode, rightContains, rightType⟩ := second.stored_type
        obtain ⟨mode, profile⟩ := BinaryProfile.of_typing operatorTyped
        exact ⟨leftNode, rightNode, mode, lookupExpression?_complete unique leftContains,
          lookupExpression?_complete unique rightContains, leftType.trans rightType.symm,
          leftType ▸ first, rightType ▸ second, leftType ▸ (resultEq ▸ profile)⟩


private theorem product_projection {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | literal receipt =>
    obtain ⟨original, originalFound, literal⟩ := receipt
    have same := Option.some.inj (originalFound.symm.trans found)
    subst original
    rcases lowered with ⟨type, code⟩
    cases literal with
    | unit _ type | bool _ _ type | word _ _ type => rw [type]; rfl
    | resolvedWord _ metadata => rw [metadata.nodeType]; rfl
    | resolvedInteger _ metadata => rw [metadata.nodeType]; rfl
  | read receipt =>
    obtain ⟨certificate, typeEq, _⟩ := receipt
    have same := Option.some.inj (certificate.metadata.found.symm.trans found)
    rw [← same, ← typeEq]
    exact certificate.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    exact same ▸ metadata.projected

theorem Tree.projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | product child => exact product_projection child found
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
