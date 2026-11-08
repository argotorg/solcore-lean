import Solcore.SourceSemantics.Internal.Inference.Subtrees
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Inference.ExpressionDispatch
import Solcore.SourceSemantics.Internal.Inference.ExpressionCalls

/-!
# Children of a selected expression

Recursive child typing needs only the selected occurrence subtree, and coercion attachment keeps the
occurrence edges.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAttachmentTransport
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend.SourceInference TypeSystem

/-- Coercion attachment preserves the actual occurrence edges even at the
expression roots whose type and coercion records it updates. -/
theorem attachExpressionCoercions_nodeReferences
    (state : State) (entries : List Detail.ExpressionCoercions)
    {node : Node} (member : node ∈ state.nodes) :
    ∃ attached ∈ (Detail.attachExpressionCoercions state entries).nodes,
      attached.id = node.id ∧ nodeChildIds attached = nodeChildIds node := by
  induction entries generalizing state node with
  | nil => exact ⟨node, member, rfl, rfl⟩
  | cons entry entries induction =>
    let changed := state.modifyExpressionNode entry.expression fun node =>
      Detail.appendExpressionCoercions node entry.coercions
    have one : ∃ next ∈ changed.nodes,
        next.id = node.id ∧ nodeChildIds next = nodeChildIds node := by
      cases node with
      | statement node =>
        refine ⟨.statement node, ?_, rfl, rfl⟩
        exact List.mem_map.mpr ⟨.statement node, member, rfl⟩
      | expression node =>
        by_cases same : node.id = entry.expression
        · refine ⟨.expression { Detail.appendExpressionCoercions node
            entry.coercions with id := entry.expression }, ?_, ?_, rfl⟩
          · exact List.mem_map.mpr ⟨.expression node, member,
              by simp [same]⟩
          · exact congrArg NodeId.expression same.symm
        · refine ⟨.expression node, ?_, rfl, rfl⟩
          exact List.mem_map.mpr ⟨.expression node, member,
            by simp [same]⟩
    obtain ⟨next, nextMember, sameId, sameChildren⟩ := one
    obtain ⟨attached, attachedMember, attachedId, attachedChildren⟩ :=
      induction changed nextMember
    exact ⟨attached, attachedMember, attachedId.trans sameId,
      attachedChildren.trans sameChildren⟩

theorem attachExpressionCoercions_directChild
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) {parent child : NodeId}
    (edge : DirectChild (state.toTypedSource roots) parent child) :
    DirectChild ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent child := by
  obtain ⟨node, contains, childMember⟩ := edge
  obtain ⟨attached, member, same, children⟩ :=
    attachExpressionCoercions_nodeReferences state entries contains.1
  exact ⟨attached, ⟨member, same.trans contains.2⟩, children ▸ childMember⟩

theorem attachExpressionCoercions_descends
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) {parent child : NodeId}
    (path : Descends (state.toTypedSource roots) parent child) :
    Descends ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent child := by
  induction path with
  | direct edge => exact .direct (attachExpressionCoercions_directChild state entries roots edge)
  | step edge _ next =>
    exact .step (attachExpressionCoercions_directChild state entries roots edge) next

theorem SubtreePreserved.directChild
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId}
    (preserved : SubtreePreserved substitution before after root)
    (edge : DirectChild before root child) : DirectChild after root child := by
  obtain ⟨node, contains, member⟩ := edge
  refine ⟨node.applySubstitution substitution, ⟨?_, ?_⟩, ?_⟩
  · exact preserved.nodes node contains.1 (.inl contains.2)
  · simpa using contains.2
  · simpa [nodeChildIds] using member

theorem SubtreePreserved.descends
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId} (path : Descends before root child) :
    SubtreePreserved substitution before after root → Descends after root child := by
  induction path with
  | direct edge => intro preserved; exact .direct (preserved.directChild edge)
  | step edge _ next =>
      intro preserved
      exact .step (preserved.directChild edge) (next (preserved.child edge))

/-- Distinct operand positions in a closed occurrence tree cannot occur
inside each other. This also excludes a position from its own descendants. -/
theorem sibling_not_descends
    {source : TypedSource} {parent left right : NodeId}
    (closed : OccurrenceGraphClosed source)
    (leftEdge : DirectChild source parent left)
    (rightEdge : DirectChild source parent right) :
    ¬ Descends source left right := by
  intro path
  obtain ⟨lastParent, lastEdge, priorPath⟩ := path.final_edge
  have same : lastParent = parent :=
    closed.childHasUniqueParent lastEdge rightEdge
  subst lastParent
  rcases priorPath with same | priorPath
  · subst left
    exact closed.acyclic parent (.direct leftEdge)
  · exact closed.acyclic parent (.step leftEdge priorPath)

private theorem attach_containsStatement
    (state : State) (entries : List Detail.ExpressionCoercions)
    {id : StatementId} {node : StatementNode} (roots : List NodeId)
    (contains : ContainsStatement (state.toTypedSource roots) id node) :
    ContainsStatement
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      id node := by
  induction entries generalizing state with
  | nil => simpa [Detail.attachExpressionCoercions] using contains
  | cons entry entries induction =>
    apply induction
    refine ⟨?_, contains.2⟩
    change Node.statement node ∈ state.nodes.map _
    exact List.mem_map.mpr ⟨.statement node, contains.1, rfl⟩

private theorem attach_owner
    (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).owner = state.owner := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
    exact induction (state.modifyExpressionNode entry.expression fun node =>
      Detail.appendExpressionCoercions node entry.coercions)

theorem rawProperDescendantsPreserved_attachExpressionCoercions
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId)
    (disjoint : ∀ entry ∈ entries,
      ¬ Descends (state.toTypedSource roots) root (.expression entry.expression)) :
    RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root := by
  refine ⟨attach_owner state entries, ?_⟩
  intro node member path
  cases node with
  | expression node =>
    have absent : node.id ∉ entries.map (·.expression) := by
      intro present
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp present
      exact disjoint entry entryMember (by simpa [same, Node.id] using path)
    exact (attachExpressionCoercions_containsExpression_of_not_mem state
      entries node.id node roots absent ⟨member, rfl⟩).1
  | statement node =>
    exact (attach_containsStatement state entries roots ⟨member, rfl⟩).1

/-- Actual coercion attachment changes only its named expression roots.
Every proper descendant outside that exact row retains its full record. -/
theorem properDescendantsPreserved_attachExpressionCoercions
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId) (substitution : Substitution)
    (disjoint : ∀ entry ∈ entries,
      ¬ Descends (state.toTypedSource roots) root (.expression entry.expression)) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots)
      (((Detail.attachExpressionCoercions state entries).toTypedSource roots
        ).applySubstitution substitution) root := by
  refine ⟨attach_owner state entries, ?_⟩
  intro node member path
  apply List.mem_map.mpr
  refine ⟨node, ?_, rfl⟩
  cases node with
  | expression node =>
    have absent : node.id ∉ entries.map (·.expression) := by
      intro present
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp present
      exact disjoint entry entryMember (by simpa [same, Node.id] using path)
    exact (attachExpressionCoercions_containsExpression_of_not_mem state
      entries node.id node roots absent ⟨member, rfl⟩).1
  | statement node =>
    exact (attach_containsStatement state entries roots ⟨member, rfl⟩).1

/-- A real operand edge and the final occurrence tree discharge disjointness
for an ordered row of sibling coercion targets. -/
theorem properDescendantsPreserved_attach_siblings
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root parent : NodeId) (substitution : Substitution)
    (evidenceSource : TypedSource)
    (closed : OccurrenceGraphClosed evidenceSource)
    (rootEdge : DirectChild evidenceSource parent root)
    (entryEdges : ∀ entry ∈ entries,
      DirectChild evidenceSource parent (.expression entry.expression))
    (paths : ∀ child, Descends (state.toTypedSource roots) root child →
      Descends evidenceSource root child) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots)
      (((Detail.attachExpressionCoercions state entries).toTypedSource roots
        ).applySubstitution substitution) root := by
  apply properDescendantsPreserved_attachExpressionCoercions
  intro entry member path
  exact sibling_not_descends closed rootEdge (entryEdges entry member)
    (paths _ path)

/-- The actual final tree discharges attachment disjointness. The path
transport is derived from the attachment action and its retained subtree. -/
theorem rawProperDescendantsPreserved_attach_final
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root parent : NodeId) (substitution : Substitution)
    (finalSource : TypedSource)
    (closed : OccurrenceGraphClosed finalSource)
    (rootEdge : DirectChild finalSource parent root)
    (entryEdges : ∀ entry ∈ entries,
      DirectChild finalSource parent (.expression entry.expression))
    (retained : SubtreePreserved substitution
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      finalSource root) :
    RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root := by
  apply rawProperDescendantsPreserved_attachExpressionCoercions
  intro entry member path
  exact sibling_not_descends closed rootEdge (entryEdges entry member)
    (SubtreePreserved.descends
      (attachExpressionCoercions_descends state entries roots path) retained)

theorem SubtreePreserved.before_attachment
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId)
    {substitution : Substitution} {after : TypedSource}
    (preserved : SubtreePreserved substitution
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) after root)
    (unchanged : RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots) after root := by
  refine ⟨preserved.owner_eq.trans unchanged.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (unchanged.nodes node member path)
    (.inr (attachExpressionCoercions_descends state entries roots path))

theorem RawSubtreePreserved.before_attachment
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId) {after : TypedSource}
    (preserved : RawSubtreePreserved
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) after root)
    (unchanged : RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root) :
    RawProperDescendantsPreserved (state.toTypedSource roots) after root := by
  refine ⟨preserved.owner_eq.trans unchanged.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (unchanged.nodes node member path)
    (.inr (attachExpressionCoercions_descends state entries roots path))

/-- The raw form is typed using exactly the retained proper descendants;
the original root record continues to supply its own requirements. -/
theorem ExpressionTypingBase.transportSemanticChildren
    {before after : TypedSource} {context : Context}
    {substitution : Substitution} {inferred : InferredExpression}
    (base : ExpressionTypingBase before (before.applySubstitution substitution)
      context substitution inferred)
    (preserved : ProperDescendantsPreserved substitution before after
      (.expression inferred.id)) :
    ExpressionTypingBase before after context substitution inferred := by
  cases base with
  | intro contains typeEq formType rawAdmissible requirements =>
    refine .intro contains typeEq (preserved.subgraph.form formType ?_)
      rawAdmissible requirements
    intro child member
    apply Descends.direct
    refine ⟨_, ⟨contains.1, ?_⟩, ?_⟩
    · exact congrArg NodeId.expression contains.2
    · simpa [nodeChildIds, Node.references] using member

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedChildSoundness
/-! Recursive child typing only needs the selected occurrence subtree in the
final evidence and the semantic carrier. Earlier sibling roots may differ. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ProperDescendantsPreserved.childSubtree
    {substitution : Substitution} {before after : TypedSource} {root child : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (edge : DirectChild before root child) : SubtreePreserved substitution before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member
    (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

theorem FinalInferenceResources.finalExpressionTypeAdmissible_in_active
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {node : ExpressionNode} {id : ExpressionId} {active : SourceSemantics.Context}
    (contains : ContainsExpression finalized.typedSource id node)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration = some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active node.type := by
  have member := contains.1
  rw [resources.source_eq] at member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  cases original with
  | expression original =>
    have sameNode : original.applySubstitution finalized.substitution = node := Node.expression.inj same
    rw [← sameNode]
    exact resources.expressionTypeAdmissible_in_active originalMember
      binders signaturesEq parametersEq ownerEq residual
  | statement original => cases same

def ActualInferExprFuelFinalSubtreeSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression inferred.id) →
    SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type)

theorem actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
    {fuel : Nat} (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelFinalSubtreeSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultPreserved finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  have finalNodes : ExpressionNodesPreservedAt [inferred.id]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    have same : id = inferred.id := by simpa using member
    subst id
    exact finalPreserved.subgraph.containsExpression contains (.inl rfl)
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id := by
    intro node requirement contains member
    have found := finalNodes (by simp)
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains)
    apply found.primaryRequirementOccursAt
    simpa [ExpressionNode.applySubstitution] using member
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt finalNodes
  have base := retainedSound success resources interfaces resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved.proper rawProper integerPatternsSubset integerLiteralsSubset
    requirementsSubset requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    (ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    childrenRetained covered
    resultPreserved.proper actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have finalContains := finalNodes (by simp)
        (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains)
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.finalExpressionTypeAdmissible_in_active
          finalContains
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [ExpressionNode.applySubstitution, typeEq] using nodeAdmissible
      have semanticNodes : ExpressionNodesPreservedAt [inferred.id]
          ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
          semanticSource := by
        intro id selected member found
        have same : id = inferred.id := by simpa using member
        subst id
        exact resultPreserved.subgraph.containsExpression found (.inl rfl)
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType semanticNodes finalAdmissible


end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ProperDescendantsPreserved.monoBefore
    {substitution : Substitution} {before middle after : TypedSource} {root : NodeId}
    (preserved : ProperDescendantsPreserved substitution middle after root)
    (extension : TypingSourceExtends before middle) :
    ProperDescendantsPreserved substitution before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  have path' : Descends middle root node.id := by
    suffices all : ∀ {start finish}, Descends before start finish → Descends middle start finish from all path
    intro start finish path
    induction path with
    | direct edge =>
      obtain ⟨node, contains, member⟩ := edge
      exact .direct ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩
    | step edge _ next =>
      obtain ⟨node, contains, member⟩ := edge
      exact .step ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩ next
  exact preserved.nodes node (extension.nodes_prefix.subset member) path'

theorem SubtreePreserved.expressionNode
    {substitution : Substitution} {before after : TypedSource} {id : ExpressionId}
    (preserved : SubtreePreserved substitution before after (.expression id)) :
    ExpressionNodesPreservedAt [id] (before.applySubstitution substitution) after := by
  intro foundId node member contains
  have same : foundId = id := by simpa using member
  subst foundId
  exact preserved.subgraph.containsExpression contains (.inl rfl)

/-- The actual argument attachment retains the facts needed to recurse into
its original child. The operand root itself may gain coercion metadata. -/
structure AttachedChildPreserved (substitution : Substitution)
    (before semantic final rawEvidence : TypedSource) (id : ExpressionId) : Prop where
  semantic : ProperDescendantsPreserved substitution before semantic (.expression id)
  finalized : ProperDescendantsPreserved substitution before final (.expression id)
  raw : RawProperDescendantsPreserved before rawEvidence (.expression id)
  requirements : ExpressionRequirementsRetainedAt before final id
  coercions : ExpressionCoercionPrimariesRetainedAt before final id
  operators : ExpressionOperatorSiteRetainedAt before final id
  children : ExpressionDirectChildrenRetainedAt before final id

namespace AttachedChildPreserved

theorem monoBefore
    {substitution : Substitution} {before middle semantic final rawEvidence : TypedSource}
    {id : ExpressionId}
    (preserved : AttachedChildPreserved substitution middle semantic final rawEvidence id)
    (extension : TypingSourceExtends before middle) :
    AttachedChildPreserved substitution before semantic final rawEvidence id :=
  ⟨preserved.semantic.monoBefore extension, preserved.finalized.monoBefore extension,
    preserved.raw.monoBefore extension,
    ExpressionRequirementsRetainedAt.monoBefore extension preserved.requirements,
    ExpressionCoercionPrimariesRetainedAt.monoBefore extension preserved.coercions,
    ExpressionOperatorSiteRetainedAt.monoBefore extension preserved.operators,
    ExpressionDirectChildrenRetainedAt.monoBefore extension preserved.children⟩

theorem of_attachment
    (state : State) (entries : List Detail.ExpressionCoercions) (roots : List NodeId)
    {substitution : Substitution} {parent : ExpressionId}
    {parentSource semantic final rawEvidence : TypedSource}
    (extension : TypingSourceExtends
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) parentSource)
    (unique : (entries.map (·.expression)).Nodup)
    (edges : ∀ entry ∈ entries,
      DirectChild parentSource (.expression parent) (.expression entry.expression))
    (semanticPreserved : ProperDescendantsPreserved substitution parentSource semantic (.expression parent))
    (finalPreserved : ProperDescendantsPreserved substitution parentSource final (.expression parent))
    (rawPreserved : RawProperDescendantsPreserved parentSource rawEvidence (.expression parent))
    (children : ExpressionDirectChildrenRetainedAt parentSource final parent)
    (closed : OccurrenceGraphClosed final)
    (entry : Detail.ExpressionCoercions) (member : entry ∈ entries) :
    AttachedChildPreserved substitution (state.toTypedSource roots)
      semantic final rawEvidence entry.expression := by
  have edge := edges entry member
  have finalRoot := (finalPreserved.childSubtree edge).monoBefore extension
  have semanticRoot := (semanticPreserved.childSubtree edge).monoBefore extension
  have rawRoot := (rawPreserved.childSubtree edge).monoBefore extension
  have untouched := rawProperDescendantsPreserved_attach_final state entries roots
    (.expression entry.expression) (.expression parent) substitution final closed
    (children edge) (fun other member => children (edges other member)) finalRoot
  have present : ExpressionNodesPreservedAt [entry.expression]
      (((Detail.attachExpressionCoercions state entries).toTypedSource roots).applySubstitution substitution)
      final := finalRoot.expressionNode
  refine ⟨semanticRoot.before_attachment state entries roots _ untouched,
    finalRoot.before_attachment state entries roots _ untouched,
    rawRoot.before_attachment state entries roots _ untouched,
    ExpressionRequirementsRetainedAt.ofAttachExpressionCoercions unique member present,
    ?_, ?_, ?_⟩
  · exact ExpressionCoercionPrimariesRetainedAt.trans
      (ExpressionCoercionPrimariesRetainedAt.ofAttachExpressionCoercions unique member)
      (ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt substitution present)
  · exact ExpressionOperatorSiteRetainedAt.trans
      (ExpressionOperatorSiteRetainedAt.ofAttachExpressionCoercions unique member)
      (ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt substitution present)
  · exact ExpressionDirectChildrenRetainedAt.trans
      (ExpressionDirectChildrenRetainedAt.ofAttachExpressionCoercions state entries roots _)
      (ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt present)

end AttachedChildPreserved
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprsFuelFinalSubtreeSoundness : ∀ fuel : Nat,
    (∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) →
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expressions : List Syntax.Expr}
    {initial resultState evidenceState : State}
    {inferred : List InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext expressions initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression argument.id)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression argument.id)) →
    (∀ argument ∈ inferred, RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression argument.id)) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered finalized.typedSource semanticContext
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes semanticSource semanticContext (inferred.map (·.id))
      (inferred.map fun argument => finalized.substitution.apply argument.type) := by
  intro fuel
  induction fuel with
  | zero =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
    simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
      resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical invariant actual operational
      semanticPreserved finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
      covered actualCovered
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil semanticContext
    | cons expression rest =>
      unfold Detail.inferExprsFuel at success
      cases headSuccess : Detail.inferExprFuel fuel inferenceContext expression none initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨head, headState⟩
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext rest headState with
        | error error => simp [tailSuccess] at success
        | ok pair =>
          rcases pair with ⟨tail, tailState⟩
          simp only [tailSuccess, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready
            signatureFormation functionsCanonical (by simp) headSuccess
          have tailProperties := Detail.inferExprsFuel_inferenceProperties headProperties.2.1
            signatureFormation functionsCanonical tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have headInvariant := invariant.ofExpression signatureFormation functionsCanonical
            (by simp) headExtension headSuccess
          have headOperational := operational.ofExpression headSuccess headProperties.1.next_le
          have headToFinal := inferExprsFuel_success_typingSourceExtends_under_bound
            tailSuccess headInvariant.nodesBelow roots
          have headTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
            (recursive fuel (Nat.lt_succ_self fuel)) headSuccess resources interfaces headExtension
            signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation functionsCanonical
            catalog canonical invariant actual operational (by simp) (by simp)
            ((semanticPreserved head (by simp)).monoBefore headToFinal)
            ((finalPreserved head (by simp)).monoBefore headToFinal)
            ((rawProper head (by simp)).monoBefore headToFinal)
            (List.Subset.trans (Detail.inferExprsFuel_integerPatterns_subset tailSuccess) integerPatternsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_integerLiterals_subset tailSuccess) integerLiteralsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_requirements_subset tailSuccess) requirementsSubset)
            (covered head (by simp)) (actualCovered head (by simp))
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
            tailSuccess resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
            signatureFormation functionsCanonical catalog canonical headInvariant actual headOperational
            (fun argument member => semanticPreserved argument (List.mem_cons_of_mem _ member))
            (fun argument member => finalPreserved argument (List.mem_cons_of_mem _ member))
            (fun argument member => rawProper argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons headTyped tailTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedBuiltinCall
/-! Builtin calls use their fixed signatures and the actual synthetic callee.
Only the descendant records of the call are needed in the semantic carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private def builtinMetadata (state : State) :=
  (state.owner, state.integerPatterns, state.integerLiterals)

private theorem unify_builtinMetadata {state next : State} {left right : Ty}
    (success : Detail.unify state left right = .ok next) :
    builtinMetadata next = builtinMetadata state := by
  unfold Detail.unify at success
  cases unified : state.inference.unify left right <;>
    simp [Detail.liftUnification, unified, bind, Except.bind] at success
  cases success
  rfl

private theorem unifyBuiltinArguments_metadata
    {arguments : List InferredExpression} {parameters : List Ty} {state next : State}
    (success : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok next) :
    builtinMetadata next = builtinMetadata state := by
  induction arguments generalizing parameters state next with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at success
    subst next
    rfl
  | cons argument arguments induction =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at success
      subst next
      rfl
    | cons parameter parameters =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual] at success
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [unified, bind, Except.bind] at success
      | ok unifiedState =>
        simp only [unified, bind, Except.bind] at success
        exact (induction success).trans (unify_builtinMetadata unified)

theorem recordBuiltinFunctionCall_metadata
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : Detail.recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.owner = state.owner ∧ result.2.integerPatterns = state.integerPatterns ∧
      result.2.integerLiterals = state.integerLiterals := by
  have metadata : builtinMetadata result.2 = builtinMetadata state := by
    unfold Detail.recordBuiltinFunctionCall at success
    by_cases arity : arguments.length = function.parameterTypes.length
    · simp only [arity, ↓reduceIte, bind, Except.bind] at success
      cases fitted : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
      | error error => simp [fitted] at success
      | ok fittedState =>
        simp only [fitted] at success
        have fittedMetadata := unifyBuiltinArguments_metadata fitted
        cases expected with
        | none =>
          simp only [pure, Except.pure, Except.ok.injEq] at success
          subst result
          exact fittedMetadata
        | some expected =>
          cases unified : Detail.unify fittedState function.returnType expected with
          | error error => simp [unified] at success
          | ok unifiedState =>
            simp only [unified, pure, Except.pure, Except.ok.injEq] at success
            subst result
            exact (unify_builtinMetadata unified).trans fittedMetadata
    · simp [arity, bind, Except.bind] at success
  exact ⟨congrArg Prod.fst metadata, congrArg (fun row => row.2.1) metadata,
    congrArg (fun row => row.2.2) metadata⟩

theorem recordBuiltinFunctionCall_expressionTypingBase_actual
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {recorded : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {semanticSource : TypedSource}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (success : Detail.recordBuiltinFunctionCall source callee name function
      arguments call expected state = .ok recorded)
    (substitutionExtends : substitution.SemanticallyExtends
      recorded.2.inference.substitution)
    (preserved : ProperDescendantsPreserved substitution
      (recorded.2.toTypedSource roots) semanticSource (.expression recorded.1.id))
    (argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      (arguments.map fun argument => substitution.apply argument.type))
    (binders : TypeParameterBindersWellFormed active) :
    ExpressionTypingBase (recorded.2.toTypedSource roots) semanticSource
      active substitution recorded.1 := by
  obtain ⟨calleeId, nodesEq⟩ :=
    Detail.recordBuiltinFunctionCall_success_nodes success
  let calleeNode : ExpressionNode := {
    id := calleeId
    span := callee.span
    type := function.type
    form := .reference name (.builtinFunction function)
  }
  let callNode : ExpressionNode := {
    id := recorded.1.id
    span := source.span
    type := recorded.1.type
    form := .call calleeId (arguments.map (·.id))
      (.builtinFunction function)
  }
  have rawCalleeContains : ContainsExpression
      (recorded.2.toTypedSource roots) calleeId calleeNode := by
    refine ⟨?_, rfl⟩
    change .expression calleeNode ∈ recorded.2.nodes
    rw [nodesEq]
    simp [calleeNode]
  have rawCallContains : ContainsExpression
      (recorded.2.toTypedSource roots) recorded.1.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ recorded.2.nodes
    rw [nodesEq]
    simp [callNode]
  have calleeEdge : DirectChild (recorded.2.toTypedSource roots)
      (.expression recorded.1.id) (.expression calleeId) := by
    refine ⟨.expression callNode, ⟨rawCallContains.1, rfl⟩, ?_⟩
    simp [callNode, nodeChildIds, Node.references, ExpressionForm.references]
  have finalCalleeContains : ContainsExpression semanticSource calleeId
      (calleeNode.applySubstitution substitution) :=
    (preserved.childSubtree calleeEdge).subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution rawCalleeContains) (.inl rfl)
  have calleeValid : DirectBuiltinCalleeValid semanticSource calleeId
      function := by
    refine .intro (name := name) finalCalleeContains ?_ ?_ ?_ ?_
    · rfl
    · cases function <;> rfl
    · rfl
    · rfl
  have argumentTypesEq :=
    Detail.recordBuiltinFunctionCall_success_argumentTypes_apply_eq success
      substitutionExtends
  have finalArgumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id)) function.parameterTypes := by
    rw [← argumentTypesEq]
    exact argumentsType
  have formType : ExpressionFormHasRawType semanticSource active
      (callNode.applySubstitution substitution).form function.returnType
      (.ordinary []) := by
    simpa [callNode, ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution, CallResolution.applySubstitution] using
        (ExpressionFormHasRawType.builtinCall calleeValid finalArgumentsType)
  have rawAdmissible : TypeAdmissible active function.returnType :=
    TypeAdmissible.builtinFunctionResult binders function
  have resultTypeEq :=
    Detail.recordBuiltinFunctionCall_success_returnType_eq success
  have finalTypeEq : substitution.apply recorded.1.type =
      function.returnType := by
    rw [resultTypeEq]
    cases function <;> rfl
  refine .intro rawCallContains rfl formType rawAdmissible ?_
  apply ExpressionRequirementPlan.Valid.ordinary
  · simp [RequirementIdsValid]
  · change CoercionPathValid active function.returnType
      (substitution.apply recorded.1.type) []
    rw [finalTypeEq]
    exact .nil _
  · rfl


theorem actualBuiltinCall_typing {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression callee : Syntax.Expr} {expected : Option Ty}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    {initial argumentState resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext argumentSources initial = .ok (arguments, argumentState) →
    Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression callee expected argumentSources arguments
    name function call initial argumentState resultState evidenceState
    inferred roots finalized semanticSource frames semanticContext argumentsSuccess
    recording resources interfaces resultSubstitutionExtension signaturesEq ownerEq
    typeParametersEq assumptionsEq signatureFormation functionsCanonical catalog canonical invariant
    actual operational expectedBelow expectedAdmissible finalPreserved rawProper integerPatternsSubset
    integerLiteralsSubset requirementsSubset retained coercionsRetained _operatorsRetained childrenRetained covered
    semanticPreserved actualCovered
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have recordProperties := Detail.recordBuiltinFunctionCall_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 expectedAtArguments recording
  have argumentExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have metadata := recordBuiltinFunctionCall_metadata recording
  obtain ⟨calleeId, nodesEq⟩ := Detail.recordBuiltinFunctionCall_success_nodes recording
  have argumentToParent : TypingSourceExtends (argumentState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change argumentState.nodes <+: resultState.nodes
    rw [nodesEq]
    exact List.prefix_append _ _
  let callNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .call calleeId (arguments.map (·.id)) (.builtinFunction function)
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) inferred.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ resultState.nodes
    rw [nodesEq]
    simp [callNode]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2]
    exact integerLiteralsSubset
  have argumentRequirements := List.Subset.trans
    (Detail.recordBuiltinFunctionCall_requirements_subset recording) requirementsSubset
  have argumentsTyped := actualInferExprsFuelFinalSubtreeSoundness fuel recursive
    argumentsSuccess resources interfaces argumentExtension signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical invariant actual operational
    (fun argument member => (semanticPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => (finalPreserved.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    (fun argument member => ((rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent).proper)
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (childrenRetained (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (childrenRetained (argumentEdge argument member)))
  exact recordBuiltinFunctionCall_expressionTypingBase_actual recording resultSubstitutionExtension
    semanticPreserved argumentsTyped
    (invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical))

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCallDiscovery
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem inferExprFuel_call_constructorDiscovery
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    {result : InferredExpression × State}
    (expressionEq : expression.value = .call callee arguments)
    (success : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Detail.constructorCalleeCandidates context initial.allocateExpressionId.2 callee = .ok [] ∨
      ∃ dataType constructor,
        Detail.constructorCalleeCandidates context initial.allocateExpressionId.2 callee =
          .ok [(dataType, constructor)] := by
  generalize allocationEq : initial.allocateExpressionId = allocatedPair at *
  rcases allocatedPair with ⟨id, allocated⟩
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates context allocated callee with
  | error error => simp [discovery] at success
  | ok candidates =>
      cases candidates with
      | nil => exact .inl rfl
      | cons first rest =>
          rcases first with ⟨dataType, constructor⟩
          cases rest with
          | nil => exact .inr ⟨dataType, constructor, rfl⟩
          | cons second tail => simp [discovery] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedConstructorArguments
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferConstructorArgumentsFuelTypes {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {sources : List Syntax.Expr} {expectedTypes : List Ty}
    {initial resultState evidenceState : State} {inferred : List InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource} {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context},
    Detail.inferConstructorArgumentsFuel fuel inferenceContext sources expectedTypes initial = .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next) →
    (∀ type ∈ expectedTypes, TypeAdmissible semanticContext (finalized.substitution.apply type)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression argument.id)) →
    (∀ argument ∈ inferred, SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource (.expression argument.id)) →
    (∀ argument ∈ inferred, RawProperDescendantsPreserved
      (resultState.toTypedSource roots) (evidenceState.toTypedSource roots) (.expression argument.id)) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered finalized.typedSource semanticContext (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes semanticSource semanticContext (inferred.map (·.id))
      (expectedTypes.map finalized.substitution.apply) := by
  intro wholeContext inferenceContext wholeReturn sources
  induction sources with
  | nil =>
    intro expectedTypes initial resultState evidenceState inferred roots finalized semanticSource frames semanticContext
      success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions
      catalog canonical invariant actual operational expectedBelow expectedAdmissible semantic final raw patterns literals
      requirements covered actualCovered
    cases expectedTypes with
    | nil =>
      simp only [Detail.inferConstructorArgumentsFuel, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      exact .nil _
    | cons _ _ => simp [Detail.inferConstructorArgumentsFuel] at success
  | cons source sources induction =>
    intro expectedTypes initial resultState evidenceState inferred roots finalized semanticSource frames semanticContext
      success resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq formation functions
      catalog canonical invariant actual operational expectedBelow expectedAdmissible semantic final raw patterns literals
      requirements covered actualCovered
    cases expectedTypes with
    | nil => simp [Detail.inferConstructorArgumentsFuel] at success
    | cons expected expectedTypes =>
      unfold Detail.inferConstructorArgumentsFuel at success
      cases headSuccess : Detail.inferExprFuel fuel inferenceContext source
          (some (initial.resolve expected)) initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok headPair =>
        obtain ⟨head, headState⟩ := headPair
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel inferenceContext sources expectedTypes headState with
        | error error => simp [tailSuccess] at success
        | ok tailPair =>
          obtain ⟨tail, tailState⟩ := tailPair
          simp only [tailSuccess, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          obtain ⟨rfl, rfl⟩ := success
          have expectedHeadBelow := expectedBelow expected (by simp)
          have headExpectedBelow : ∀ type ∈ some (initial.resolve expected), type.VariablesBelow initial.inference.next := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            subst type
            exact invariant.ready.solved.variablesBelow_apply expectedHeadBelow
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation functions
            headExpectedBelow headSuccess
          have tailExpectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow headState.inference.next :=
            fun type member => (expectedBelow type (by simp [member])).weaken headProperties.1.next_le
          have tailProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties
            headProperties.2.1 formation functions tailExpectedBelow tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have initialExtension := headExtension.trans headProperties.1.substitution_extends
          have initialResolved : finalized.substitution.apply (initial.resolve expected) =
              finalized.substitution.apply expected := by
            simpa only [State.resolve, InferState.resolve] using initialExtension expected
          have headExpectedAdmissible : ∀ type ∈ some (initial.resolve expected),
              TypeAdmissible semanticContext (finalized.substitution.apply type) := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            rw [same, initialResolved]
            exact expectedAdmissible expected (by simp)
          have headInvariant := invariant.ofExpression formation functions headExpectedBelow headExtension headSuccess
          have headOperational := operational.ofExpression headSuccess headProperties.1.next_le
          have headToFinal := inferConstructorArgumentsFuel_success_typingSourceExtends
            tailSuccess headInvariant.nodesBelow roots
          have headTyped := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
            headSuccess resources interfaces headExtension signaturesEq ownerEq typeParametersEq assumptionsEq
            formation functions catalog canonical invariant actual operational headExpectedBelow headExpectedAdmissible
            ((semantic head (by simp)).monoBefore headToFinal)
            ((final head (by simp)).monoBefore headToFinal)
            ((raw head (by simp)).monoBefore headToFinal)
            ((Detail.inferConstructorArgumentsFuel_integerPatterns_subset tailSuccess).trans patterns)
            ((Detail.inferConstructorArgumentsFuel_integerLiterals_subset tailSuccess).trans literals)
            ((Detail.inferConstructorArgumentsFuel_requirements_subset tailSuccess).trans requirements)
            (covered head (by simp)) (actualCovered head (by simp))
          have headTypeEq : finalized.substitution.apply head.type = finalized.substitution.apply expected := by
            exact (Detail.inferExprFuel_expected_type_apply_eq headSuccess headExtension).trans initialResolved
          have tailTyped := induction tailSuccess resources interfaces extension signaturesEq ownerEq typeParametersEq
            assumptionsEq formation functions catalog canonical headInvariant actual headOperational tailExpectedBelow
            (fun type member => expectedAdmissible type (by simp [member]))
            (fun argument member => semantic argument (by simp [member]))
            (fun argument member => final argument (by simp [member]))
            (fun argument member => raw argument (by simp [member])) patterns literals requirements
            (fun argument member => covered argument (by simp [member]))
            (fun argument member => actualCovered argument (by simp [member]))
          exact .cons (by simpa only [headTypeEq] using headTyped) tailTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPlaceSoundness
/-! Mapping-key inference retains the actual generalized-initializer scope.
Each recursive key is selected by its original place reference. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem sourcePlace_type_admissible {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {type : Ty} (typed : SourcePlaceHasType source context place type) :
    TypeAdmissible context type := by
  have projections {before after : Ty} {projections : List PlaceProjection}
      (typed : SourceProjectionsHaveType source context before projections after)
      (valid : TypeAdmissible context before) : TypeAdmissible context after := by
    induction projections generalizing before after with
    | nil => cases typed; exact valid
    | cons projection rest induction =>
      cases typed with
      | index key tail => exact induction tail (TypeAdmissible.mapping_value valid)
      | member selected tail => exact induction tail selected.member_type_admissible
  cases typed with
  | intro root rest _ => exact projections rest root.type_admissible

theorem ActualStateInvariant.ofPlace
    {fuel : Nat} {context : Frontend.SourceInference.Context} {target : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferPlaceFuel fuel context target initial = .ok (place, final))
    (nextLe : initial.inference.next ≤ final.inference.next) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have bindersEq := congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq success)
  exact ⟨⟨pending, (actualLedgerFamily fuel).place success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

def ActualInferPlaceFuelRootedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {targetExpression : Syntax.Expr}
    {initial final parentState evidenceState : State}
    {place : PlaceResolution} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferPlaceFuel fuel inferenceContext targetExpression initial =
      .ok (place, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    finalized.substitution.SemanticallyExtends
      final.inference.substitution →
    TypingSourceExtends (final.toTypedSource roots)
      (parentState.toTypedSource roots) →
    (∀ key, .expression key ∈ place.references →
      RawSubtreePreserved (parentState.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.expression key)) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    (∀ key, .expression key ∈ place.references →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.expression key)) →
    (∀ key, .expression key ∈ place.references →
      ActualContext.Covers finalized frames (.expression key)) →
    SourcePlaceHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext (place.applySubstitution finalized.substitution)
      (finalized.substitution.apply place.type)

theorem actualInferPlaceFuelRootedSoundness :
    ∀ fuel, (∀ childFuel, childFuel < fuel →
      ActualInferExprFuelRootedSoundness childFuel) →
      ActualInferPlaceFuelRootedSoundness fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ wholeContext inferenceContext wholeReturn targetExpression
        initial final parentState evidenceState place roots finalized
        frames semanticContext success
      simp [Detail.inferPlaceFuel] at success
  | succ fuel induction =>
      intro expressionSound wholeContext inferenceContext wholeReturn
        targetExpression initial final parentState evidenceState place roots
        finalized frames semanticContext success resources interfaces signaturesEq ownerEq
        parametersEq assumptionsEq signatureFormation functionsCanonical
        catalog signatureParameters invariant actual operational finalSubstitutionExtension
        finalToParent rawParentToEvidence patternsSubset literalsSubset
        requirementsSubset keysCovered keysActualCovered
      cases targetEq : targetExpression.value
      case identifier name =>
        exact inferPlaceFuel_success_identifier_sound targetEq success
          invariant.active finalSubstitutionExtension
      case group inner =>
        have innerSuccess : Detail.inferPlaceFuel fuel inferenceContext inner
            initial = .ok (place, final) := by
          simpa only [Detail.inferPlaceFuel, targetEq] using success
        exact induction
          (fun childFuel childLt => expressionSound childFuel
            (Nat.lt_trans childLt (Nat.lt_succ_self fuel)))
          innerSuccess resources interfaces signaturesEq ownerEq parametersEq
          assumptionsEq signatureFormation functionsCanonical catalog
          signatureParameters invariant actual operational finalSubstitutionExtension
          finalToParent rawParentToEvidence patternsSubset literalsSubset
          requirementsSubset keysCovered keysActualCovered
      case index base brackets key =>
        obtain ⟨basePlace, baseState, keyInitial, inferredKey, baseSuccess,
            baseInvariant, unifySuccess, keySuccess, placeEq, keyInvariant,
            keyExpectedBelow, keyMember⟩ :=
          inferPlaceFuel_index_key_invariant targetEq success
            signatureFormation functionsCanonical invariant
            finalSubstitutionExtension
        obtain ⟨actualBasePlace, actualBaseState, actualBaseSuccess,
            _baseBelow, baseToFinal, baseLiteralsToFinal,
            basePatternsToFinal, baseRequirementsToFinal⟩ :=
          inferPlaceFuel_success_index_base_state_provenance targetEq
            success invariant.nodesBelow roots
        rw [baseSuccess] at actualBaseSuccess
        obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualBaseSuccess).symm
        have baseToParent : TypingSourceExtends
            (baseState.toTypedSource roots)
            (parentState.toTypedSource roots) :=
          baseToFinal.trans finalToParent
        have baseKeysCovered : ∀ keyId,
            .expression keyId ∈ basePlace.references →
              TemplateScopeCovered finalized.typedSource semanticContext
                (.expression keyId) := by
          intro keyId member
          exact keysCovered keyId
            (inferPlaceFuel_index_base_references_subset targetEq
              baseSuccess success member)
        have baseTyped : SourcePlaceHasType
            ((parentState.toTypedSource roots).applySubstitution
              finalized.substitution) semanticContext
            (basePlace.applySubstitution finalized.substitution)
            (finalized.substitution.apply basePlace.type) :=
          induction
            (fun childFuel childLt => expressionSound childFuel
              (Nat.lt_trans childLt (Nat.lt_succ_self fuel)))
            baseSuccess resources interfaces signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters invariant actual operational baseInvariant.substitutionExtension
            baseToParent (fun keyId member => rawParentToEvidence keyId
              (inferPlaceFuel_index_base_references_subset targetEq baseSuccess success member))
            (List.Subset.trans basePatternsToFinal patternsSubset)
            (List.Subset.trans baseLiteralsToFinal literalsSubset)
            (List.Subset.trans baseRequirementsToFinal requirementsSubset)
            baseKeysCovered (fun keyId member => keysActualCovered keyId
              (inferPlaceFuel_index_base_references_subset targetEq baseSuccess success member))
        have baseProperties := Detail.inferPlaceFuel_inferenceProperties invariant.ready signatureFormation functionsCanonical baseSuccess
        have baseOperational := operational.ofPlace baseSuccess baseProperties.1.next_le
        have keyOperational := baseOperational.fresh.fresh.unify unifySuccess
        have baseEq : finalized.substitution.apply basePlace.type =
            .mapping (finalized.substitution.apply baseState.fresh.1)
              (finalized.substitution.apply baseState.fresh.2.fresh.1) := by
          calc
            finalized.substitution.apply basePlace.type = finalized.substitution.apply (keyInitial.resolve basePlace.type) := by
              simpa only [State.resolve, InferState.resolve] using (keyInvariant.substitutionExtension basePlace.type).symm
            _ = finalized.substitution.apply (keyInitial.resolve (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)) :=
              congrArg finalized.substitution.apply (Detail.unify_resolve_eq unifySuccess)
            _ = .mapping (finalized.substitution.apply baseState.fresh.1)
                  (finalized.substitution.apply baseState.fresh.2.fresh.1) := by
              simpa only [State.resolve, InferState.resolve, Substitution.apply] using
                keyInvariant.substitutionExtension (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)
        have keyExpectedAdmissible : ∀ type ∈ (some (keyInitial.resolve baseState.fresh.1) : Option Ty),
            TypeAdmissible semanticContext (finalized.substitution.apply type) := by
          intro type member
          have same : type = keyInitial.resolve baseState.fresh.1 := Option.some.inj member.symm
          subst type
          have resolved : finalized.substitution.apply (keyInitial.resolve baseState.fresh.1) =
              finalized.substitution.apply baseState.fresh.1 := by
            simpa only [State.resolve, InferState.resolve] using keyInvariant.substitutionExtension baseState.fresh.1
          rw [resolved]
          have valid := sourcePlace_type_admissible baseTyped
          rw [baseEq] at valid
          exact TypeAdmissible.mapping_key valid
        have keyExpectedBound :
            ∀ expectedType ∈
              (some (keyInitial.resolve baseState.fresh.1) : Option Ty),
              expectedType.VariablesBelow keyInitial.inference.next := by
          intro expectedType member
          simp only [Option.mem_def] at member
          cases member
          exact keyExpectedBelow
        have keyTyped : ExpressionHasType
            ((parentState.toTypedSource roots).applySubstitution
              finalized.substitution) semanticContext inferredKey.id
            (finalized.substitution.apply inferredKey.type) :=
          expressionSound fuel (Nat.lt_succ_self fuel) keySuccess resources interfaces
            finalSubstitutionExtension signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters keyInvariant actual keyOperational keyExpectedBound keyExpectedAdmissible
            (SubtreePreserved.ofTypingSourceExtends
              (finalToParent.applySubstitution finalized.substitution))
            ((rawParentToEvidence inferredKey.id keyMember).monoBefore finalToParent)
            patternsSubset literalsSubset requirementsSubset
            (keysCovered inferredKey.id keyMember) (keysActualCovered inferredKey.id keyMember)
        exact inferPlaceFuel_index_sound_of_actual_typed_children
          baseSuccess unifySuccess keySuccess placeEq
          keyInvariant.substitutionExtension finalSubstitutionExtension
          baseTyped keyTyped
      all_goals simp [Detail.inferPlaceFuel, targetEq] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedRetainedExpressionList
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprsFuelRetainedBases : ∀ fuel : Nat,
    (∀ smaller, smaller < fuel → ActualInferExprFuelRetainedSoundness smaller) →
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expressions : List Syntax.Expr}
    {initial resultState evidenceState : State}
    {inferred : List InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprsFuel fuel inferenceContext expressions initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ argument ∈ inferred, AttachedChildPreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource finalized.typedSource
      (evidenceState.toTypedSource roots) argument.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered finalized.typedSource semanticContext
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers finalized frames (.expression argument.id)) →
    ArgumentTypingBasesValid (resultState.toTypedSource roots) semanticSource semanticContext
      finalized.substitution inferred := by
  intro fuel
  induction fuel with
  | zero =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
    simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
    intro recursive wholeContext inferenceContext wholeReturn expressions initial
      resultState evidenceState inferred roots finalized semanticSource frames semanticContext success
      resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
      signatureFormation functionsCanonical catalog canonical invariant actual operational
      preserved integerPatternsSubset integerLiteralsSubset requirementsSubset
      covered actualCovered
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil
    | cons expression rest =>
      unfold Detail.inferExprsFuel at success
      cases headSuccess : Detail.inferExprFuel fuel inferenceContext expression none initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨head, headState⟩
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext rest headState with
        | error error => simp [tailSuccess] at success
        | ok pair =>
          rcases pair with ⟨tail, tailState⟩
          simp only [tailSuccess, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready
            signatureFormation functionsCanonical (by simp) headSuccess
          have tailProperties := Detail.inferExprsFuel_inferenceProperties headProperties.2.1
            signatureFormation functionsCanonical tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have headInvariant := invariant.ofExpression signatureFormation functionsCanonical
            (by simp) headExtension headSuccess
          have headOperational := operational.ofExpression headSuccess headProperties.1.next_le
          have headToFinal := inferExprsFuel_success_typingSourceExtends_under_bound
            tailSuccess headInvariant.nodesBelow roots
          have headPreserved := (preserved head (by simp)).monoBefore headToFinal
          have headTyped := (recursive fuel (Nat.lt_succ_self fuel))
            headSuccess resources interfaces headExtension signaturesEq ownerEq typeParametersEq assumptionsEq
            signatureFormation functionsCanonical catalog canonical invariant actual operational (by simp) (by simp)
            headPreserved.finalized headPreserved.raw
            (List.Subset.trans (Detail.inferExprsFuel_integerPatterns_subset tailSuccess) integerPatternsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_integerLiterals_subset tailSuccess) integerLiteralsSubset)
            (List.Subset.trans (Detail.inferExprsFuel_requirements_subset tailSuccess) requirementsSubset)
            headPreserved.requirements headPreserved.coercions headPreserved.operators headPreserved.children
            (covered head (by simp)) headPreserved.semantic (actualCovered head (by simp))
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
            tailSuccess resources interfaces extension signaturesEq ownerEq typeParametersEq assumptionsEq
            signatureFormation functionsCanonical catalog canonical headInvariant actual headOperational
            (fun argument member => preserved argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons (headTyped.weakenNodeSource headToFinal.nodes_prefix) tailTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
end
