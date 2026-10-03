import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins

/-! A delegated group keeps the actual sanitizer and exact child code. The
changed parent is explicitly excluded from the child's reached references;
unique occurrence IDs alone do not imply that condition. No execution law is
stored in these static receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
open Core Frontend SourceInference
open CallableCoercionExpressionCertificates CallableLambdaViewEdits CallableLambdaBodyReachability

private theorem node_eq {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (first : source.lookupExpression? id = some left) (second : source.lookupExpression? id = some right) : left = right :=
  Option.some.inj (first.symm.trans second)

/-- The real replacement is found at the original occurrence, including all
of its changed type, requirement and coercion fields. -/
theorem raw_lookup {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (ordinary : List RequirementId) :
    (SourceCoreEvidence.withNode source (rawNode node ordinary)).lookupExpression? id = some (rawNode node ordinary) := by
  have sound := lookupExpression?_sound found
  have same : node.id = id := sound.2
  have self : source.lookupExpression? node.id = some node := same.symm ▸ found
  have edited := CallableLambdaViewEdits.raw unique self ordinary
  apply lookupExpression?_complete (edited.metadata.unique unique)
  constructor
  · apply List.mem_map.mpr
    refine ⟨.expression node, sound.1, ?_⟩
    simp [rawNode]
  · exact same

private theorem ordinary_empty {node : ExpressionNode}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  change (let coercions := coercionRequirementIds node.coercions
    if node.requirements.length < coercions.length then none else
      let owned := node.requirements.take (node.requirements.length - coercions.length)
      if node.requirements = owned ++ coercions then some owned else none) = some []
  simp [Dynamic.OrdinaryRequirementLayout] at layout
  simp [layout]

/-- Original independent group typing fixes the raw child type and empty
owned prefix. Retained output coercions remain in their original order. -/
theorem group_typing {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type) :
    ExpressionHasType source context inner node.rawType ∧
      TypeAdmissible context node.rawType ∧ Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq rawWF _ requirements =>
    have same := node_eq (lookupExpression?_complete unique contains) found
    subst same
    rw [form] at raw
    cases raw with
    | group child =>
      cases requirements with
      | ordinary _ _ layout =>
        refine ⟨rawEq ▸ child, rawEq ▸ rawWF, layout, ?_⟩
        exact ordinary_empty layout

/-- Only the child typing is transported. The edited root is then rebuilt with
its raw type and an empty output path using the independent typing rules. -/
theorem sanitized_typing {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type)
    (avoids : Avoids source [.expression inner] [node.id]) :
    ExpressionHasType (SourceCoreEvidence.withNode source (rawNode node [])) context id node.rawType := by
  obtain ⟨child, rawWF, _, _⟩ := group_typing unique found form typed
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound found).2.symm ▸ found
  have edited := CallableLambdaViewEdits.raw unique self []
  have childTyped := CallableLambdaViewStaticTyping.expression edited avoids unique child (.root (by simp))
  apply ExpressionHasType.ofOrdinary (lookupExpression?_sound (raw_lookup unique found []))
    (rawType := node.rawType) (owned := [])
  · simpa only [rawNode, form] using ExpressionFormHasRawType.group childTyped
  · exact rawWF
  · exact rawWF
  · exact fun id member => False.elim (List.not_mem_nil member)
  · exact .nil _
  · rfl

section Inversion
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}

private theorem products_group
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | literal receipt =>
    obtain ⟨other, selected, literal⟩ := receipt
    have same := node_eq selected found
    subst other
    generalize lowered.type = nativeType at literal
    generalize lowered.expression = code at literal
    cases literal <;> simp_all
  | read receipt =>
    obtain ⟨receipt, _, _⟩ := receipt
    have same := node_eq receipt.metadata.found found
    have other := same ▸ receipt.form
    simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem primitives_group
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | product tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := products_group tree found form
    exact ⟨child, selected, same, ordinary, .product childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem conditionals_group
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | primitive tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := primitives_group tree found form
    exact ⟨child, selected, same, ordinary, .primitive childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem constructors_group
    (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := conditionals_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm

private theorem members_group
    (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := constructors_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem recursive_group
    (tree : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := members_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem general_group
    (tree : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := recursive_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | proxy receipt =>
    cases receipt with
    | proxy header =>
      have same := node_eq header.metadata.found found
      have other := same ▸ header.form
      simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | index receipt _ otherForm _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm

private theorem builtins_group
    (tree : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := general_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | proxy receipt =>
    cases receipt with
    | proxy header =>
      have same := node_eq header.metadata.found found
      have other := same ▸ header.form
      simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | index receipt _ otherForm _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | builtin metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

end Inversion


/-- A concrete child in the original source, with the same code returned by the
actual delegated sanitizer. Its own complete builtin subtree is finite. -/
structure Child (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : Scope) (node : ExpressionNode) (inner : ExpressionId) (operand : Lowered) where
  form : node.form = .group inner
  layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []
  innerNode : ExpressionNode
  found : source.lookupExpression? inner = some innerNode
  rawType : node.rawType = innerNode.type
  tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope inner operand

section Factory
variable {program : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel readFuel : Nat}
  {source : TypedSource} {scope : Scope} {id inner : ExpressionId} {node : ExpressionNode}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} {solved : List SolvedRequirement}

/-- Extract any group placement, including the existing fragment embeddings,
then transport its complete child tree back across the real local edit. -/
theorem of_tree
    (receipt : Delegated program project caller compilation child fuel source scope id reasonAt policy node output)
    (unique : NodeOccurrencesUnique source) (form : node.form = .group inner)
    (avoids : Avoids source [.expression inner] [node.id])
    (tree : CompatibleExpressionBuiltins.Tree readFuel values
      (SourceCoreEvidence.withNode source (rawNode node receipt.ordinary)) context solved reasonAt scope id receipt.operand) :
    Nonempty (Child readFuel values source context solved reasonAt scope node inner receipt.operand) := by
  obtain ⟨innerNode, selected, sameType, empty, childTree⟩ :=
    builtins_group tree (raw_lookup unique receipt.found receipt.ordinary) (show (rawNode node receipt.ordinary).form = .group inner from form)
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound receipt.found).2.symm ▸ receipt.found
  have edited := CallableLambdaViewEdits.raw unique self receipt.ordinary
  have reached : Reaches source [.expression inner] (.expression inner) := .root (by simp)
  have originalFound := (expression_lookup edited avoids reached).trans selected
  have layout := CallableCallRequirementLayouts.ordinary_owned receipt.ordinaryAccepted
  change receipt.ordinary = [] at empty
  rw [empty] at layout
  exact ⟨⟨form, layout, innerNode, originalFound, sameType,
    CallableLambdaViewBuiltinTrees.builtins_original edited avoids childTree reached⟩⟩

/-- The production contextual callback supplies the sanitized tree. Original
source typing reconstructs raw-root typing, so there is no separate assumed
sanitized typing or child execution law. Ordinary/static scope policies remain
explicit, including the absence of local-polymorphic initializers. -/
theorem of_contextual
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (receipt : Delegated program project caller compilation child fuel source scope id reasonAt policy node output)
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (unique : NodeOccurrencesUnique source) (form : node.form = .group inner)
    (typed : ExpressionHasType source context id node.type)
    (avoids : Avoids source [.expression inner] [node.id])
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source inner)
    (ordinary : CompatibleExpressionBuiltins.Ordinary (SourceCoreEvidence.withNode source (rawNode node [])) locals compilation.owner)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (SourceCoreEvidence.withNode source (rawNode node [])) scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Child readFuel values source context compilation.solvedRequirements reasonAt scope node inner receipt.operand) := by
  have selected := (group_typing unique receipt.found form typed).2.2.2
  have empty := Option.some.inj (receipt.ordinaryAccepted.symm.trans selected)
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound receipt.found).2.symm ▸ receipt.found
  have edited := CallableLambdaViewEdits.raw unique self []
  have childSyntax := CallableLambdaViewSourceTyping.expression_syntax edited avoids unique syntaxTree (.root (by simp))
  have rawFound := raw_lookup unique receipt.found []
  have rawTyped := sanitized_typing unique receipt.found form typed avoids
  have accepted := receipt.childAccepted
  simp only [childEq, empty] at accepted
  have tree := CompatibleExpressionBuiltins.tree_of_contextual ordinary (edited.metadata.unique unique)
    closed residual declarations sourceSignatures (.group rawFound form childSyntax) rawFound rawTyped
    readPolicy lowerPolicy leafPolicy accepted
  apply of_tree receipt unique form avoids
  simpa only [empty] using tree

end Factory

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
