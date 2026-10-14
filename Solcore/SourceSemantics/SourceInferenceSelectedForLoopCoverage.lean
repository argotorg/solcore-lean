import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferenceForItemsCoverage

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem forItemsReferencesCovered_of_rootedForLoop
    {rawSource finalSource : TypedSource} {outer : Substitution}
    {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (containsRaw : ContainsStatement rawSource id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (extension : SubtreePreserved outer rawSource finalSource (.statement id))
    (closed : OccurrenceGraphClosed finalSource)
    (parentCovered : TemplateScopeCovered finalSource context
      (.statement id)) :
    ForItemsReferencesCovered finalSource outer context initializer ∧
      ForItemsReferencesCovered finalSource outer context post := by
  have containsFinal : ContainsStatement finalSource id
      (node.applySubstitution outer) :=
    extension.containsStatement containsRaw
  have finalForm : (node.applySubstitution outer).form =
      .forLoop (initializer.map (ForItemForm.applySubstitution outer))
        condition (post.map (ForItemForm.applySubstitution outer)) body := by
    simp [StatementNode.applySubstitution, formEq,
      StatementForm.applySubstitution]
  have covered := forLoop_finalHeaderReferencesCovered closed
    containsFinal finalForm parentCovered
  constructor
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
private theorem item_reference {item : ForItemForm} {binding : InitializedLetBinding}
    (member : binding ∈ forItemInitializedLetBindings item) :
    binding.initializer ∈ item.references := by
  cases item with
  | letDecl binder value =>
    cases value with
    | none => simp [forItemInitializedLetBindings] at member
    | some value =>
      simp only [forItemInitializedLetBindings, List.mem_singleton] at member
      subst binding
      simp [ForItemForm.references]
  | expression _ | assignValue _ _ _ | assignBitNot _ =>
    simp [forItemInitializedLetBindings] at member

private theorem statement_reference {form : StatementForm} {binding : InitializedLetBinding}
    (member : binding ∈ statementInitializedLetBindings form) :
    binding.initializer ∈ form.references := by
  cases form with
  | letDecl binder value =>
    cases value with
    | none => simp [statementInitializedLetBindings] at member
    | some value =>
      simp only [statementInitializedLetBindings, List.mem_singleton] at member
      subst binding
      simp [StatementForm.references]
  | forLoop initializer condition post body =>
    simp only [statementInitializedLetBindings, List.mem_append] at member
    rcases member with member | member
    all_goals
      obtain ⟨item, present, member⟩ := List.mem_flatMap.mp member
      have reference := item_reference member
      simp only [StatementForm.references, List.mem_append, List.mem_cons]
    · exact .inl (.inl (.inl (List.mem_flatMap.mpr ⟨item, present, reference⟩)))
    · exact .inl (.inr (List.mem_flatMap.mpr ⟨item, present, reference⟩))
  | returnStmt _ | expression _ _ | assignValue _ _ _ | assignBitNot _
    | ifThen _ _ _ | block _ | matchWith _ | whileLoop _ _ | breakStmt | continueStmt =>
    simp [statementInitializedLetBindings] at member

/-- Membership in the original statement's binder list yields the literal
closed binder and its edge in the same final source. -/
theorem actualBinding_of_rootedStatement
    {before : TypedSource} {id : StatementId} {node : StatementNode}
    {finalized : Frontend.SourceInference.Result} {binding : InitializedLetBinding}
    (recorded : ContainsStatement before id node)
    (extension : SubtreePreserved finalized.substitution before finalized.typedSource (.statement id))
    (member : binding ∈ statementInitializedLetBindings node.form) :
    let closed := FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding
    closed ∈ initializedLetBindings finalized.typedSource ∧
      DirectChild finalized.typedSource (.statement id) closed.initializer := by
  have retained := extension.containsStatement recorded
  have closedMember : FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding ∈
      statementInitializedLetBindings (node.form.applySubstitution finalized.substitution) := by
    rw [FlexibleSubstitution.statementInitializedLetBindings_applySubstitution]
    exact List.mem_map_of_mem member
  constructor
  · unfold initializedLetBindings
    exact List.mem_flatMap.mpr ⟨.statement (node.applySubstitution finalized.substitution), retained.1, closedMember⟩
  · refine ⟨.statement (node.applySubstitution finalized.substitution),
      ⟨retained.1, congrArg NodeId.statement retained.2⟩, ?_⟩
    exact statement_reference closedMember

/-- Both header lists obtain scope provenance from their original enclosing
loop, including initialized binders whose template-requirement list is empty. -/
theorem actualForItemsBindings_of_rootedForLoop
    {before : TypedSource} {id : StatementId} {span : Syntax.SourceSpan} {type : Ty}
    {initializer post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    (recorded : ContainsStatement before id {id, span, type, form := .forLoop initializer condition post body})
    (extension : SubtreePreserved finalized.substitution before finalized.typedSource (.statement id))
    (covered : ActualContext.Covers finalized frames (.statement id)) :
    ActualForItemsBindings finalized frames initializer ∧ ActualForItemsBindings finalized frames post := by
  have all : ∀ binding ∈ statementInitializedLetBindings (.forLoop initializer condition post body),
      let closed := FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding
      closed ∈ initializedLetBindings finalized.typedSource ∧
        ∀ outer ∈ frames, Descends finalized.typedSource outer.initializer closed.initializer := by
    intro binding member
    obtain ⟨retained, edge⟩ := actualBinding_of_rootedStatement recorded extension member
    refine ⟨retained, ?_⟩
    intro outer present
    rcases covered outer present with same | below
    · exact same ▸ Descends.direct edge
    · exact below.trans (.direct edge)
  constructor
  · intro item present binding member
    exact all binding (by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact .inl (List.mem_flatMap.mpr ⟨item, present, member⟩))
  · intro item present binding member
    exact all binding (by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact .inr (List.mem_flatMap.mpr ⟨item, present, member⟩))


theorem RawSubtreePreserved.containsStatement
    {before after : TypedSource} {id : StatementId} {node : StatementNode}
    (preserved : RawSubtreePreserved before after (.statement id))
    (contains : ContainsStatement before id node) : ContainsStatement after id node := by
  refine ⟨preserved.nodes (.statement node) contains.1 (.inl ?_), contains.2⟩
  simpa [Node.id] using congrArg NodeId.statement contains.2

end Solcore.SourceSemantics.SourceInferenceSoundness
