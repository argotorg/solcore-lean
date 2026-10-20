import Solcore.SourceSemantics.SourceInferenceNormalizedContracts

/-! Recording joins a real expression result to its actual expected fit.
Capture facts are restricted through the exact recorded node table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail

theorem expression_allocation_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial) :
    allocated.InferenceReady ∧ allocated.NodesBelowNextOccurrence ∧
      NormalizedStateFormation semantic outer allocated ∧
      allocated.inference = initial.inference := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact ⟨State.InferenceReady.allocateExpressionId ready,
    State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes,
    formed.congr rfl rfl, rfl⟩

theorem statement_allocation_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial) :
    allocated.InferenceReady ∧ allocated.NodesBelowNextOccurrence ∧
      NormalizedStateFormation semantic outer allocated ∧
      allocated.inference = initial.inference := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact ⟨State.InferenceReady.allocateStatementId ready,
    State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodes,
    formed.congr rfl rfl, rfl⟩

theorem NoCaptureNodes.before_recordNode
    {outer : Substitution} {state : State} {node : Node}
    (capture : NoCaptureNodes outer (state.recordNode node).nodes) :
    NoCaptureNodes outer state.nodes :=
  capture.of_prefix (List.prefix_append _ _)

theorem NormalizedStateFormation.recordNode
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {state : State} (formed : NormalizedStateFormation semantic outer state) (node : Node) :
    NormalizedStateFormation semantic outer (state.recordNode node) :=
  formed.congr rfl rfl

theorem NormalizedStateFormation.unify
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} {left right : Ty}
    (formed : NormalizedStateFormation semantic outer before)
    (accepted : Detail.unify before left right = .ok after) :
    NormalizedStateFormation semantic outer after :=
  formed.congr (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (unify_requirements_eq accepted)

theorem NoCaptureNodes.before_unify
    {outer : Substitution} {before after : State} {left right : Ty}
    (capture : NoCaptureNodes outer after.nodes)
    (accepted : Detail.unify before left right = .ok after) :
    NoCaptureNodes outer before.nodes := by
  rwa [(unify_occurrenceState_eq accepted).1] at capture

theorem NoCaptureNodes.before_recordExpressionWithExpected
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (capture : NoCaptureNodes outer result.2.nodes)
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    NoCaptureNodes outer state.nodes := by
  obtain ⟨fitted, fit, _, nodes⟩ := recordExpressionWithExpected_success_nodes accepted
  rw [nodes, (withExpected_occurrenceState_eq fit).1] at capture
  exact capture.of_prefix (List.prefix_append _ _)

theorem recordExpressionWithExpected_normalized_state
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (typeFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have produced := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation typeFormed expectedFormed accepted
  exact ⟨produced.1, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_recordExpressionWithExpected_lexicalScope accepted)) produced.2⟩

theorem normalized_productMany
    {semantic : SourceSemantics.Context} {outer : Substitution} {types : List Ty}
    (binders : TypeParameterBindersWellFormed semantic)
    (formed : ∀ type ∈ types, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply (Ty.productMany types)) := by
  rw [Substitution.apply_productMany]
  apply TypeAdmissible.productMany binders
  intro type member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact formed original present

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
