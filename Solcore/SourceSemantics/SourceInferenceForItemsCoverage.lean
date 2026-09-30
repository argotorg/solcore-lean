import Solcore.SourceSemantics.SourceInferenceForItemsScopedSoundness

/-!
Coverage of the actual references in a recorded `for` header.  Unlike an
ordinary statement child, a generalized header initializer introduces local
scheme assumptions.  Unique child slots identify the exact header item whose
binder owns those assumptions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

private theorem eq_of_common_mem_of_flatMap_nodup
    {α β : Type} (f : α → List β)
    {values : List α} {left right : α} {value : β}
    (unique : (values.flatMap f).Nodup)
    (leftMem : left ∈ values) (rightMem : right ∈ values)
    (leftValue : value ∈ f left) (rightValue : value ∈ f right) :
    left = right := by
  induction values generalizing left right with
  | nil => simp at leftMem
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.nodup_append] at unique
      rcases unique with ⟨_, tailUnique, separated⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          exact separated value leftValue value
            (List.mem_flatMap.mpr ⟨right, rightMem, rightValue⟩) rfl
      · rcases rightMem with rfl | rightMem
        · exfalso
          exact separated value rightValue value
            (List.mem_flatMap.mpr ⟨left, leftMem, leftValue⟩) rfl
        · exact ih tailUnique leftMem rightMem leftValue rightValue

/-- Forgetting the condition and body slots of a closed `for` node still
leaves a globally unique source-ordered header reference inventory. -/
private theorem forLoop_header_references_nodup
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body) :
    ((initializer ++ post).flatMap ForItemForm.references).Nodup := by
  have slots := closed.childSlotsUnique (.statement node) contains.1
  simp only [nodeChildIds, Node.references, formEq,
    StatementForm.references] at slots
  simp only [List.append_assoc] at slots
  have initUnique : (initializer.flatMap ForItemForm.references).Nodup :=
    (List.nodup_append.mp slots).1
  have restUnique := (List.nodup_append.mp slots).2.1
  have postUnique : (post.flatMap ForItemForm.references).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp restUnique).2.1).1
  have separated := (List.nodup_append.mp slots).2.2
  have combined :
      (initializer.flatMap ForItemForm.references ++
        post.flatMap ForItemForm.references).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨initUnique, postUnique, ?_⟩
    intro value initMember value' postMember eq
    apply separated value initMember value'
    · exact List.mem_append_right _
        (List.mem_append_left _ postMember)
    · exact eq
  simpa [List.flatMap_append] using combined

private theorem forItem_binding_initializer_mem_references
    {item : ForItemForm} {binding : InitializedLetBinding}
    (member : binding ∈ forItemInitializedLetBindings item) :
    binding.initializer ∈ item.references := by
  cases item with
  | letDecl binder initializer =>
      cases initializer with
      | none => simp [forItemInitializedLetBindings] at member
      | some initializer =>
          have bindingEq : binding = {
              binder := binder, initializer := .expression initializer } := by
            simpa [forItemInitializedLetBindings] using member
          subst binding
          simp [ForItemForm.references]
  | expression _ => simp [forItemInitializedLetBindings] at member
  | assignValue _ _ _ => simp [forItemInitializedLetBindings] at member
  | assignBitNot _ => simp [forItemInitializedLetBindings] at member

/-- Any qualified template whose root is a reference of one selected header
item must be owned by a binding of that very item.  The graph's unique parent
identifies the enclosing statement; unique child slots identify the item. -/
private theorem forLoop_template_binding_of_item_reference
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {item : ForItemForm} {reference : NodeId}
    {owner : LocalSchemeTemplateOwner}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (itemMem : item ∈ initializer ++ post)
    (referenceMem : reference ∈ item.references)
    (ownerContains : ContainsLocalSchemeTemplate source owner)
    (initializerEq : owner.initializer = reference) :
    ({ binder := owner.binder, initializer := owner.initializer } :
      InitializedLetBinding) ∈ forItemInitializedLetBindings item := by
  have bindingMem := owner.binding_mem ownerContains
  obtain ⟨ownerNode, ownerNodeContains, ownerBindingMem, ownerEdge⟩ :=
    InitializedLetBinding.owningStatement bindingMem
  have selectedEdge : DirectChild source (.statement id) reference := by
    refine ⟨.statement node, ?_, ?_⟩
    · exact ⟨contains.1, congrArg NodeId.statement contains.2⟩
    · have headerMem : reference ∈
          (initializer ++ post).flatMap ForItemForm.references :=
        List.mem_flatMap.mpr ⟨item, itemMem, referenceMem⟩
      have either : reference ∈ initializer.flatMap ForItemForm.references ∨
          reference ∈ post.flatMap ForItemForm.references := by
        simpa [List.flatMap_append] using headerMem
      have full : reference ∈
          (StatementForm.forLoop initializer condition post body).references := by
        simp only [StatementForm.references, List.mem_append]
        rcases either with initialRef | postRef
        · exact Or.inl (Or.inl (Or.inl initialRef))
        · exact Or.inl (Or.inr postRef)
      simpa [nodeChildIds, Node.references, formEq] using full
  have parentEq : ownerNode.id = id := by
    have parentsEq := closed.childHasUniqueParent
      (by simpa [initializerEq] using ownerEdge) selectedEdge
    cases parentsEq
    rfl
  have nodeEq : ownerNode = node := by
    have ownerLookup := lookupStatement?_complete
      closed.wellFormed.nodeOccurrencesUnique ownerNodeContains
    have selectedLookup := lookupStatement?_complete
      closed.wellFormed.nodeOccurrencesUnique contains
    rw [parentEq, selectedLookup] at ownerLookup
    exact Option.some.inj ownerLookup.symm
  subst ownerNode
  have bindingInHeaders :
      ({ binder := owner.binder, initializer := owner.initializer } :
        InitializedLetBinding) ∈
        (initializer ++ post).flatMap forItemInitializedLetBindings := by
    simpa [formEq, statementInitializedLetBindings,
      List.flatMap_append] using ownerBindingMem
  rcases List.mem_flatMap.mp bindingInHeaders with
    ⟨ownerItem, ownerItemMem, ownerItemBindingMem⟩
  have ownerReference : reference ∈ ownerItem.references := by
    simpa [initializerEq] using
      forItem_binding_initializer_mem_references ownerItemBindingMem
  have itemEq : item = ownerItem :=
    eq_of_common_mem_of_flatMap_nodup ForItemForm.references
      (forLoop_header_references_nodup closed contains formEq)
      itemMem ownerItemMem referenceMem ownerReference
  simpa [itemEq] using ownerItemBindingMem

private theorem forLoop_header_directChild
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {item : ForItemForm} {reference : NodeId}
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (itemMem : item ∈ initializer ++ post)
    (referenceMem : reference ∈ item.references) :
    DirectChild source (.statement id) reference := by
  refine ⟨.statement node, ?_, ?_⟩
  · exact ⟨contains.1, congrArg NodeId.statement contains.2⟩
  · have headerMem : reference ∈
        (initializer ++ post).flatMap ForItemForm.references :=
      List.mem_flatMap.mpr ⟨item, itemMem, referenceMem⟩
    have either : reference ∈ initializer.flatMap ForItemForm.references ∨
        reference ∈ post.flatMap ForItemForm.references := by
      simpa [List.flatMap_append] using headerMem
    have full : reference ∈
        (StatementForm.forLoop initializer condition post body).references := by
      simp only [StatementForm.references, List.mem_append]
      rcases either with initialRef | postRef
      · exact Or.inl (Or.inl (Or.inl initialRef))
      · exact Or.inl (Or.inr postRef)
    simpa [nodeChildIds, Node.references, formEq] using full

/-- Every reference in the recorded final `for` header is covered.  The
context of a generalized let initializer carries precisely its own qualified
scheme predicates; all other references inherit the loop context. -/
theorem forLoop_finalHeaderReferencesCovered
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (parentCovered : TemplateScopeCovered source context (.statement id)) :
    ∀ item, item ∈ initializer ++ post → ∀ reference,
      reference ∈ item.references →
      TemplateScopeCovered source
        (match item with
         | .letDecl binder (some _) =>
             localSchemeInitializerContext context binder
         | _ => context)
        reference := by
  intro item itemMem reference referenceMem
  have edge : DirectChild source (.statement id) reference :=
    forLoop_header_directChild contains formEq itemMem referenceMem
  cases item with
  | letDecl binder initializerId =>
      cases initializerId with
      | none => simp [ForItemForm.references] at referenceMem
      | some initializerId =>
          have referenceEq : reference = .expression initializerId := by
            simpa [ForItemForm.references] using referenceMem
          subst reference
          apply TemplateScopeCovered.localSchemeInitializer_of_newRoots
            parentCovered closed.childHasUniqueParent edge
          intro owner ownerContains ownerInitializerEq
          have bindingMem := forLoop_template_binding_of_item_reference
            closed contains formEq itemMem
            (by simp [ForItemForm.references]) ownerContains
            ownerInitializerEq
          have binderEq : owner.binder = binder := by
            have bindingEq :
                ({ binder := owner.binder, initializer := owner.initializer } :
                  InitializedLetBinding) = {
                    binder := binder, initializer := .expression initializerId
                  } := by
              simpa [forItemInitializedLetBindings] using bindingMem
            exact congrArg InitializedLetBinding.binder bindingEq
          simpa [binderEq] using owner.requirement_mem ownerContains
  | expression expression =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem
  | assignValue assignment operator value =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem
  | assignBitNot assignment =>
      apply TemplateScopeCovered.child parentCovered
        closed.childHasUniqueParent edge (fun _ member => member)
      intro owner ownerContains ownerInitializerEq
      have bindingMem := forLoop_template_binding_of_item_reference
        closed contains formEq itemMem referenceMem ownerContains
        ownerInitializerEq
      simp [forItemInitializedLetBindings] at bindingMem

/-- The actual recorded raw loop, together with final substitution and
append-only source growth, discharges both coverage premises passed to the
initializer and post-item recursive traversals.  This theorem does not assume
that unrelated arbitrary children are covered. -/
theorem forItemsReferencesCovered_of_recordedForLoop
    {rawSource finalSource : TypedSource} {outer : Substitution}
    {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (containsRaw : ContainsStatement rawSource id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (extension : TypingSourceExtends
      (rawSource.applySubstitution outer) finalSource)
    (closed : OccurrenceGraphClosed finalSource)
    (parentCovered : TemplateScopeCovered finalSource context
      (.statement id)) :
    ForItemsReferencesCovered finalSource outer context initializer ∧
      ForItemsReferencesCovered finalSource outer context post := by
  have containsFinal : ContainsStatement finalSource id
      (node.applySubstitution outer) :=
    extension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
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
end Solcore.SourceSemantics.SourceInferenceSoundness
