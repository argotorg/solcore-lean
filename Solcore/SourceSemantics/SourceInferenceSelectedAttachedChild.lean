import Solcore.SourceSemantics.SourceInferenceSelectedAttachmentTransport
import Solcore.SourceSemantics.SourceInferenceSelectedChildSoundness
import Solcore.SourceSemantics.SourceInferenceExecutableOperatorRetention

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
