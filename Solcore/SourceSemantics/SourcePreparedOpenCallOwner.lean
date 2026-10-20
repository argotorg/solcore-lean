import Solcore.SourceSemantics.SourcePreparedCatalogedCallOrigin

/-! Open source calls use an actually discovered local instance of the same
original selected row. Closed/direct source scans cannot provide that edge. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedOpenCallOwner
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourcePreparedOpenCallEdges

private theorem same_expression {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {left right : ExpressionNode} (leftMember : .expression left ∈ source.nodes)
    (rightMember : .expression right ∈ source.nodes) (same : left.id = right.id) : left = right := by
  have leftFound := lookupExpression?_complete unique ⟨leftMember, rfl⟩
  have rightFound := lookupExpression?_complete unique ⟨rightMember, rfl⟩
  rw [same] at leftFound
  exact Option.some.inj (leftFound.symm.trans rightFound)

private theorem direct_closed {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource} {edge : CallEdge}
    (receipt : CallEdge.DirectReceipt program caller source edge) :
    InstantiationClosed receipt.instantiation = true := by
  have closed := receipt.closed
  change (match (match receipt.node.form with
    | .call _ _ (.declaration instantiation) => some instantiation
    | .reference _ (.declaration instantiation) => some instantiation
    | _ => none) with
      | some instantiation => !(((instantiation.type ::
          instantiation.parameterSubstitution.map Prod.snd ++
          instantiation.predicates.flatMap (fun predicate => predicate.subject :: predicate.arguments)).flatMap
            Ty.freeVariables).eraseDups).isEmpty
      | none => false) = false at closed
  rw [receipt.form] at closed
  simp only at closed
  have empty : ((receipt.instantiation.type ::
      receipt.instantiation.parameterSubstitution.map Prod.snd ++
      receipt.instantiation.predicates.flatMap (fun predicate => predicate.subject :: predicate.arguments)).flatMap
        Ty.freeVariables).eraseDups = [] := by
    exact List.isEmpty_iff.mp ((show ∀ value : Bool, (!value) = false → value = true by decide) _ closed)
  have erase_nil : ∀ values : List TypeVarId, values.eraseDups = [] → values = [] := by
    intro values given
    cases values with
    | nil => rfl
    | cons head tail => simp only [List.eraseDups_cons, List.cons_ne_nil] at given
  have empty := erase_nil _ empty
  simp only [List.flatMap_cons, List.append_eq_nil_iff, List.flatMap_append] at empty
  unfold InstantiationClosed
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true]
  refine ⟨⟨empty.1.1, ?_⟩, ?_⟩
  · intro entry present
    have all := List.flatMap_eq_nil_iff.mp empty.1.2
    exact all _ (List.mem_map.mpr ⟨entry, present, rfl⟩)
  · intro predicate present
    have all := List.flatMap_eq_nil_iff.mp empty.2
    have subject := all predicate.subject (List.mem_flatMap.mpr ⟨predicate, present, List.mem_cons_self⟩)
    refine ⟨subject, ?_⟩
    intro argument occurs
    exact all argument (List.mem_flatMap.mpr ⟨predicate, present, List.mem_cons_of_mem _ occurs⟩)

structure Contextual (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializationKey) (source : TypedSource)
    (node : ExpressionNode) (edge : CallEdge)
    extends CallEdge.ContextualReceipt program caller source edge where
  sameNode : node.applySubstitution localInstance.substitution = receipt.node

/-- The same original call is in the actual lexical body whose template
ownership checks succeeded for this discovered instance. -/
theorem Contextual.body {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource}
    {node : ExpressionNode} {edge : CallEdge}
    (contextual : Contextual program caller source node edge)
    (unique : NodeOccurrencesUnique source) (present : .expression node ∈ source.nodes) :
    ∃ nodes, localLambdaBodyNodes source contextual.localInstance = .ok nodes ∧
      .expression node ∈ nodes ∧
      LocalTemplateUses (localLambdaBindings source) contextual.localInstance nodes := by
  obtain ⟨original, nodes, accepted, originalMember, transformed⟩ := contextual.toContextualReceipt.original_body
  obtain ⟨checkedNodes, checked, subset, templates⟩ :=
    localLambdaInstances_template_receipts contextual.discovered contextual.localInstance contextual.member
  have same := Except.ok.inj (accepted.symm.trans checked)
  subst checkedNodes
  have sameId := congrArg ExpressionNode.id (transformed.trans contextual.sameNode.symm)
  change original.id = node.id at sameId
  have same := same_expression unique (subset originalMember) present sameId
  subst original
  exact ⟨nodes, accepted, originalMember, templates⟩

/-- This is the actual contextual branch of edge discovery, including the
complete instance, substitution, and same original node. -/
theorem contextual_of_open {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializationKey} {source : TypedSource}
    (unique : NodeOccurrencesUnique source) {node : ExpressionNode}
    (present : .expression node ∈ source.nodes) {callee : ExpressionId}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (opened : InstantiationClosed instantiation = false)
    {edge : CallEdge} (origin : CallEdge.SourceOrigin program caller source edge)
    (occurrence : edge.occurrence = node.id) : Nonempty (Contextual program caller source node edge) := by
  rcases origin.receipts with direct | contextual
  · obtain ⟨receipt, member⟩ := direct
    have same := same_expression unique member present (receipt.emitted.2.1.symm.trans occurrence)
    have forms := receipt.form.symm.trans (same ▸ form)
    have sameInstantiation : receipt.instantiation = instantiation := by cases forms; rfl
    have closed := direct_closed receipt
    rw [sameInstantiation, opened] at closed
    cases closed
  · obtain ⟨contextual⟩ := contextual
    obtain ⟨original, originalMember, transformed⟩ := contextual.original
    have occurrenceEq := congrArg ExpressionNode.id transformed
    change original.id = contextual.receipt.node.id at occurrenceEq
    have same := same_expression unique originalMember present
      (occurrenceEq.trans (contextual.receipt.emitted.2.1.symm.trans occurrence))
    subst original
    exact ⟨⟨contextual, transformed⟩⟩

end Solcore.SourceSemantics.SourcePreparedOpenCallOwner
