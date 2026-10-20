import Solcore.SourceSemantics.SourceInferenceNormalizedContracts

/-! The actual local-reference branch uses only the earlier structural binder
invariant. Ledger identity receipts are unnecessary for predicate formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

private theorem normalized_predicate {outer : Substitution} {state : State}
    (continuation : outer.SemanticallyExtends state.inference.substitution)
    (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  cases predicate with
  | mk trait subject arguments =>
    simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
    congr 1
    · exact continuation subject
    · simp only [List.map_map]
      exact List.map_congr_left (fun type _ => continuation type)

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · cases List.mem_singleton.mp new
        exact .inr (by simp)
    · exact .inr (by simp [issued])

theorem inferExprFuel_local_normalized_state
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty}
    {initial allocated : State} {id : ExpressionId}
    {binder : TypedBinder} {result : InferredExpression × State}
    (formation : InferenceFormationContext semantic context outer)
    (ready : initial.InferenceReady)
    (earlier : NormalizedStateFormation semantic outer initial)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have member := (State.lookupBinder?_eq_some_facts found).1
  rw [allocatedEq] at member
  have binderFormed := earlier.binders binder member
  let instantiation := binder.scheme.instantiateWithSubstitution allocated.inference.next
  let advanced : State := {allocated with inference := {allocated.inference with next := instantiation.next}}
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiation.substitution requirement.predicate)
  let batch := advanced.addRequirementsWithIds predicates
  have progress := Detail.inferExprFuel_inferenceProperties ready formation.validated
    formation.functionShapes expectedBelow accepted
  have beforeContinuation : outer.SemanticallyExtends advanced.inference.substitution := by
    have before := continuation.trans progress.1.substitution_extends
    change outer.SemanticallyExtends allocated.inference.substitution
    rw [allocatedEq]
    exact before
  have instantiated := binderFormed.instantiate formation.toFormationContext
    formation.scope.binders allocated.inference.next
  have bodyFormed : TypeAdmissible semantic (outer.apply (advanced.resolve instantiation.body)) :=
    (beforeContinuation _).symm ▸ instantiated.1
  have predicatesFormed : ∀ predicate ∈ predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate present
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp present
    rw [normalized_predicate beforeContinuation]
    exact instantiated.2 requirement requirementMember
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation bodyFormed expectedFormed recorded
  refine ⟨fitted.1, earlier.of_new_rows
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)) ?_⟩
  apply new_normalized_requirements_trans (middle := batch.2) ?_ fitted.2
  intro row present fresh
  rcases batch_origin advanced predicates present with old | issued
  · have original : row ∈ initial.requirements := by
      change row ∈ allocated.requirements at old
      rw [allocatedEq] at old
      exact old
    exact (fresh original).elim
  · exact predicatesFormed row.predicate issued

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
