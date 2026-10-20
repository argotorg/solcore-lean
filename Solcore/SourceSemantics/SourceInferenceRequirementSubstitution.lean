import Solcore.SourceSemantics.SourceInferenceRequirementFormation

/-! Residual-aware formation transport for requirements and finalizer ranges. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

private theorem mem_freeVariables_foldl_application_iff
    (metavariable : TypeVarId) (head : Ty) (arguments : List Ty) :
    metavariable ∈ (arguments.foldl Ty.application head).freeVariables ↔
      metavariable ∈ head.freeVariables ∨
        ∃ argument, argument ∈ arguments ∧
          metavariable ∈ argument.freeVariables := by
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      rw [List.foldl_cons, induction,
        SourceSemantics.mem_freeVariables_application_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((headMember | argumentMember) | tailMember)
        · exact Or.inl headMember
        · exact Or.inr ⟨argument, Or.inl rfl, argumentMember⟩
        · rcases tailMember with ⟨candidate, candidateMember, occurs⟩
          exact Or.inr ⟨candidate, Or.inr candidateMember, occurs⟩
      · rintro (headMember | ⟨candidate, candidateMember, occurs⟩)
        · exact Or.inl (Or.inl headMember)
        · rcases candidateMember with rfl | candidateMember
          · exact Or.inl (Or.inr occurs)
          · exact Or.inr ⟨candidate, candidateMember, occurs⟩

private theorem mem_freeVariables_nominal_iff
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff]
  simp [Ty.freeVariables]

private theorem TypesWellScoped.ofEachAdmissibleWithin
    {context : Context} {types : List Ty} {outer : Ty}
    (admissible : ∀ type, type ∈ types → TypeAdmissible context type)
    (included : ∀ type, type ∈ types →
      ∀ metavariable, metavariable ∈ type.freeVariables →
        metavariable ∈ outer.freeVariables) :
    TypesWellScoped context (admissibleTypeVariables context outer) types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (TypeAdmissible.typeWellScopedWithin
          (included head (by simp)) (admissible head (by simp)))
        (induction
          (fun type member => admissible type (by simp [member]))
          (fun type member => included type (by simp [member])))

/-- An admissible flexible range preserves type formation in a context that
admits residual variables. No groundness or substitution-domain coverage is needed. -/
theorem type_applySubstitution_residual
    {context : SourceSemantics.Context} {type : Ty}
    {substitution : Substitution}
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    (formed : TypeAdmissible context type) :
    TypeAdmissible context (substitution.apply type) := by
  have binders := formed.binders
  refine TypeWellScoped.rec
    (motive_1 := fun current _ => TypeAdmissible context (substitution.apply current))
    (motive_2 := fun types _ => ∀ current ∈ types,
      TypeAdmissible context (substitution.apply current))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ formed.typeWellScoped
  · intro metavariable _
    cases found : substitution.lookup? metavariable with
    | none =>
        simpa [Substitution.apply, found] using
          TypeAdmissible.variableOfResidual binders residual metavariable
    | some replacement =>
        simpa [Substitution.apply, found] using
          range metavariable replacement (Substitution.lookup?_eq_some_mem found)
  · intro parameter bound owned
    exact ⟨binders, .parameter bound owned⟩
  · intro builtin
    exact TypeAdmissible.builtin binders builtin
  · intro dataType arguments cataloged arity _ argumentInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine ⟨binders, .nominal dataType (arguments.map substitution.apply)
      cataloged (by simpa using arity) ?_⟩
    apply TypesWellScoped.ofEachAdmissibleWithin
    · intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact argumentInduction original originalMember
    · intro argument member metavariable occurs
      exact mem_freeVariables_nominal_iff.mpr
        ⟨argument, member, occurs⟩
  · intro contract arguments cataloged arity _ argumentInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine ⟨binders, .contractNominal contract (arguments.map substitution.apply)
      cataloged (by simpa using arity) ?_⟩
    apply TypesWellScoped.ofEachAdmissibleWithin
    · intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact argumentInduction original originalMember
    · intro argument member metavariable occurs
      exact mem_freeVariables_nominal_iff.mpr
        ⟨argument, member, occurs⟩
  · intro parameter result _ _ parameterInduction resultInduction
    exact TypeAdmissible.function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact TypeAdmissible.product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact TypeAdmissible.mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.proxy innerInduction
  · intro inner _ innerInduction
    exact TypeAdmissible.comptime innerInduction
  · intro current member
    simp at member
  · intro head tail _ _ headInduction tailInduction current member
    rcases List.mem_cons.mp member with rfl | member
    · exact headInduction
    · exact tailInduction current member

/-- Predicate component formation survives an admissible flexible
substitution in the residual context used for generalized initializers. -/
theorem predicate_applySubstitution_residual
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    {substitution : Substitution}
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context substitution)
    (formed : PredicateAdmissible context predicate) :
    PredicateAdmissible context
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  constructor
  · exact type_applySubstitution_residual residual range formed.subject
  · intro argument member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact type_applySubstitution_residual residual range
      (formed.arguments original originalMember)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        have valid := formed.trait
        rw [traitEq] at valid
        simpa [TypedTraitResolution.applySubstitution, traitEq] using valid
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simp only [TypedTraitResolution.applySubstitution, traitEq]
        exact ⟨signature, member, idEq, by simpa using arity⟩

/-- A residual target can change lexical flexible scope while retaining the
same rigid declaration binders and signature catalog. -/
theorem predicate_transport_residual
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed target)
    (signatures : target.signatures = source.signatures)
    (parameters : target.typeParameters = source.typeParameters)
    (owner : target.currentDeclaration = source.currentDeclaration)
    (residual : target.residualTypeVariables = true)
    (formed : PredicateAdmissible source predicate) :
    PredicateAdmissible target predicate := by
  constructor
  · exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual binders residual
      (StructuralSubstitution.TypeWellScoped.transportContext signatures parameters owner
        formed.subject.typeWellScoped)
  · intro argument member
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual binders residual
      (StructuralSubstitution.TypeWellScoped.transportContext signatures parameters owner
        (formed.arguments argument member).typeWellScoped)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin
        simpa only [traitEq] using formed.trait
    | declaration id =>
        have valid := formed.trait
        rw [traitEq] at valid
        obtain ⟨signature, member, idEq, arity⟩ := valid
        simpa only [traitEq] using
          (show ∃ signature ∈ target.signatures.traits,
            signature.id = id ∧ predicate.arguments.length + 1 = signature.parameters.length from
            ⟨signature, signatures.symm ▸ member, idEq, arity⟩)

/-- Removing quantified quantifiers from an admissible substitution does not
introduce new replacements. -/
theorem range_without {context : SourceSemantics.Context}
    {substitution : Substitution}
    (range : SubstitutionRangeAdmissible context substitution)
    (quantified : List TypeVarId) :
    SubstitutionRangeAdmissible context (substitution.without quantified) :=
  fun metavariable replacement member =>
    range metavariable replacement (Substitution.mem_of_mem_without member)

/-- Actual finalization provides the replacement formation needed to normalize
an issued predicate. This uses its range validator without assuming ground types. -/
theorem finalizer_predicate_formation
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (parameters : context.typeParameters = inferenceContext.typeParameters)
    (owner : context.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : context.residualTypeVariables = true)
    (formed : PredicateAdmissible context predicate)
    (quantified : List TypeVarId) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution
      (result.substitution.without quantified) predicate) :=
  predicate_applySubstitution_residual residual
    (range_without (InferenceSubstitutionRangeFormationValidated.rangeAdmissible
      resources.range_formation binders signatures parameters owner residual) quantified)
    formed

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
