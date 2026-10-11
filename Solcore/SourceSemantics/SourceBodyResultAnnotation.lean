import Solcore.SourceSemantics.SubstitutionProperties

/-!
The legacy body result is either unit or a stored statement annotation.
Consequently two rigid substitutions that produce the same source agree on
that result. This follows from one original typing derivation and the ordered
source nodes; neither substituted body needs a separate typing derivation.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceBodyResultAnnotation
open Frontend SourceInference TypeSystem

private theorem statement_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType source control context id final facts) :
    ∃ node, ContainsStatement source id node ∧ facts.type = node.type := by
  cases typing
  all_goals refine ⟨_, by assumption, ?_⟩
  all_goals symm; assumption

/-- The body summary selects unit or a physically stored statement type. -/
theorem statements_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {statements : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context statements final facts) :
    facts.type = .unit ∨
      ∃ id node, ContainsStatement source id node ∧ facts.type = node.type := by
  induction statements generalizing context final facts with
  | nil => cases typing; exact Or.inl rfl
  | cons id rest ih =>
      cases typing with
      | singleton head =>
          obtain ⟨node, contained, annotation⟩ := statement_annotation head
          simp only [BodyFacts.singleton]
          split
          · exact Or.inr ⟨id, node, contained, annotation⟩
          · exact Or.inl rfl
      | cons head tail =>
          have tailAnnotation := ih tail
          obtain ⟨node, contained, annotation⟩ := statement_annotation head
          simp only [BodyFacts.cons]
          split
          · exact tailAnnotation
          · split
            · exact Or.inr ⟨id, node, contained, annotation⟩
            · exact tailAnnotation

/-- One original body derivation supplies the result annotation provenance. -/
theorem body_annotation
    {source : TypedSource} {context : Context} {result : Ty} {facts : BodyFacts}
    (typing : BodyHasType source context result facts) :
    facts.type = .unit ∨
      ∃ id node, ContainsStatement source id node ∧ facts.type = node.type := by
  obtain ⟨_, statements, _, _⟩ := typing
  exact statements_annotation statements

/-- Equal rigid instances retain the same ordered node annotations. No range
formation or occurrence-uniqueness premise is needed for this comparison. -/
theorem parameter_instances_result_eq
    {source : TypedSource} {context : Context} {result : Ty} {facts : BodyFacts}
    (typing : BodyHasType source context result facts)
    (left right : ParameterSubstitution)
    (same : StructuralSubstitution.applyTypedSource left source =
      StructuralSubstitution.applyTypedSource right source) :
    left.apply facts.type = right.apply facts.type := by
  rcases body_annotation typing with unit | ⟨id, node, contained, annotation⟩
  · rw [unit]
    rfl
  · have nodes := congrArg TypedSource.nodes same
    change source.nodes.map (StructuralSubstitution.applyNode left) =
      source.nodes.map (StructuralSubstitution.applyNode right) at nodes
    have nodeEq := (List.map_inj_left.mp nodes) (Node.statement node) contained.1
    have statementEq : StructuralSubstitution.applyStatementNode left node =
        StructuralSubstitution.applyStatementNode right node := Node.statement.inj nodeEq
    rw [annotation]
    exact congrArg StatementNode.type statementEq

end Solcore.SourceSemantics.SourceBodyResultAnnotation
