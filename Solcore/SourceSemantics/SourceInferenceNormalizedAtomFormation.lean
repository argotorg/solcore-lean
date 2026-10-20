import Solcore.SourceSemantics.SourceInferenceNormalizedDeclarationFormation

/-! Actual integer and nonlocal reference branches produce normalized result
types and every requirement issued before and during expected fitting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem allocation_requirements {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated)) :
    allocated.requirements = initial.requirements := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  rfl

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · simp only [List.mem_singleton] at new
        subst row
        exact .inr (by simp)
    · exact .inr (by simp [issued])

/-- The actual numeric branch allocates its variable and Int requirement;
final range validation forms that variable without assuming literal typing. -/
theorem inferExprFuel_numeric_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {spelling : Syntax.CoreLiteralValue} {rawValue : Nat}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .literal literal) (literalForm : literal.value = spelling)
    (decoded : Frontend.numericLiteralValue? spelling = some rawValue)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  let rawType := allocated.fresh.1
  let addition := allocated.fresh.2.addRequirementWithId (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩, expression := id, requirement := addition.1 }
  let literalState : State := {addition.2 with integerLiterals := addition.2.integerLiterals ++ [origin]}
  have rawFormed : TypeAdmissible semantic (outer.apply rawType) :=
    type_applySubstitution_residual formation.residual formation.range
      (.variableOfResidual binders formation.residual ⟨allocated.inference.next⟩)
  have recorded := (Detail.inferExprFuel_success_numericLiteral_record form literalForm decoded allocation accepted).1
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation rawFormed expectedFormed recorded
  refine ⟨fitted.1, new_normalized_requirements_trans (middle := literalState) ?_ fitted.2⟩
  intro row member fresh
  change row ∈ allocated.requirements ++
    [{id := addition.1, predicate := ProgramSignatures.builtinIntPredicate rawType}] at member
  rw [allocation_requirements allocation] at member
  rcases List.mem_append.mp member with old | introduced
  · exact (fresh old).elim
  · cases List.mem_singleton.mp introduced
    exact builtin_integer_predicate rawFormed

/-- A real named-reference lookup fixes the catalog signature whose exact
fresh batch is recorded by this successful identifier inference. -/
theorem inferExprFuel_declaration_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {signature : ProgramFunctionSignature} {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (notBoolean : (name.value == "true" || name.value == "false") = false)
    (functions : Detail.functionsNamed context name.value = .ok [signature])
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have signatureMember : signature ∈ semantic.signatures.functions := by
    rw [formation.signatures]
    exact Detail.functionsNamed_success_subset_catalog functions (by simp)
  have signatureFormed := formation.catalog.functions_semantic signature signatureMember
  let instantiated := signature.scheme.instantiate allocated.inference.next
  let advanced : State := {allocated with inference := {allocated.inference with next := instantiated.next}}
  let batch := advanced.addRequirementsWithIds instantiated.predicates
  have rawFormed : TypeAdmissible semantic (outer.apply instantiated.body) := by
    rw [ConstrainedDeclarationScheme.instantiate_body]
    apply instantiated_declaration_type_normalized formation binders signatureMember
    rw [signatureFormed.scheme_body]
    exact .function
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureFormed.parameter_types))
      (StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped signatureFormed.return_types))
  have predicatesFormed : ∀ predicate ∈ instantiated.predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate member
    exact predicate_applySubstitution_residual formation.residual formation.range
      (instantiated_function_predicates formation.catalog binders formation.residual signatureMember _ predicate member)
  have recorded := Detail.inferExprFuel_success_declarationIdentifier_record
    form allocation notLocal notBoolean functions accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation rawFormed expectedFormed recorded
  refine ⟨fitted.1, new_normalized_requirements_trans (middle := batch.2) ?_ fitted.2⟩
  intro row member fresh
  rcases batch_origin advanced instantiated.predicates member with old | introduced
  · have present : row ∈ allocated.requirements := old
    rw [allocation_requirements allocation] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate introduced

/-- Builtin Boolean references have no initial batch; only their actual
expected fitting can add requirements. -/
theorem inferExprFuel_boolean_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (isBoolean : (name.value == "true" || name.value == "false") = true)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have recorded := Detail.inferExprFuel_success_builtinBooleanIdentifier_record
    form allocation notLocal isBoolean accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation
    (type_applySubstitution_residual formation.residual formation.range (.bool binders)) expectedFormed recorded
  simpa only [allocation_requirements allocation] using fitted

/-- The actual builtin identifier lookup records its fixed admissible type
before the same successful expected fitting. -/
theorem inferExprFuel_builtin_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {function : BuiltinFunctionId} {result : InferredExpression × State}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (notLocal : allocated.lookupBinder? name.value = none)
    (notBoolean : (name.value == "true" || name.value == "false") = false)
    (functions : Detail.functionsNamed context name.value = .ok [])
    (builtin : builtinFunctionNamed? name.value = some function)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have recorded := Detail.inferExprFuel_success_builtinFunctionIdentifier_record
    form allocation notLocal notBoolean functions builtin accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation continuation
    (type_applySubstitution_residual formation.residual formation.range (.builtinFunction binders function)) expectedFormed recorded
  simpa only [allocation_requirements allocation] using fitted

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
