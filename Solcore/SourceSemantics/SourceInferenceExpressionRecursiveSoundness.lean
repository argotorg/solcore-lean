import Solcore.SourceSemantics.SourceInferenceExpressionOperatorSoundness
import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-!
The fuel-recursive expression theorem is kept downstream of both the
syntax-directed expression bridges and the corresponding statement contract.
This file first records the finalization adapters which make that mutual
interface independent of an artificial, fixed pre-substitution semantic
context.  Such a context cannot remain fixed across source-ordered `let`
bindings, whereas the final substitution's validated range is stable for the
whole body.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

private theorem mem_freeVariables_foldl_application_iff_recursive
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

private theorem mem_freeVariables_nominal_iff_recursive
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff_recursive]
  simp [Ty.freeVariables]

private theorem typesWellScoped_of_each_admissible_within
    {context : SourceSemantics.Context} {outer : Ty} {types : List Ty}
    (each : ∀ type, type ∈ types → TypeAdmissible context type)
    (included : ∀ type, type ∈ types → ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∈ outer.freeVariables) :
    TypesWellScoped context (admissibleTypeVariables context outer) types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        ((each head (by simp)).typeWellScopedWithin
          (included head (by simp)))
        (induction
          (fun type member => each type (by simp [member]))
          (fun type member => included type (by simp [member])))

/-- Applying a structurally validated inference substitution to a
structurally validated inference type produces an admissible type directly in
the active residually-open context.  Unlike the older context-closure bridge,
this statement needs no parallel unsubstituted local context and therefore
survives sequential introduction of local binders. -/
theorem inferenceTypeFormationValidated_apply_typeAdmissible
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {flexibleVariables : List TypeVarId}
    {type : Ty} {substitution : Substitution}
    {active : SourceSemantics.Context}
    (validated : InferenceTypeFormationValidated signatures owner parameters
      flexibleVariables type)
    (range : InferenceSubstitutionRangeFormationValidated signatures owner
      parameters substitution)
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = signatures)
    (parametersEq : active.typeParameters = parameters)
    (ownerEq : active.currentDeclaration = some owner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active (substitution.apply type) := by
  refine InferenceTypeFormationValidated.rec
    (motive_1 := fun current _ =>
      TypeAdmissible active (substitution.apply current))
    (motive_2 := fun types _ => ∀ current, current ∈ types →
      TypeAdmissible active (substitution.apply current))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ validated
  · intro metavariable _
    cases found : substitution.lookup? metavariable with
    | none =>
        simp only [Substitution.apply, found, Option.getD_none]
        exact TypeAdmissible.variableOfResidual binders residual metavariable
    | some replacement =>
        simp only [Substitution.apply, found, Option.getD_some]
        exact InferenceTypeFormationValidated.typeAdmissible
          (range metavariable replacement
            (TypeSystem.Substitution.lookup?_eq_some_mem found))
          binders signaturesEq parametersEq ownerEq residual
  · intro parameter bound owned
    exact {
      binders
      typeWellScoped := .parameter
        (by simpa [parametersEq] using bound)
        (ownerEq.trans (congrArg some owned.symm))
    }
  · intro builtin
    exact TypeAdmissible.builtin binders builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine {
      binders
      typeWellScoped := .nominal dataType
        (arguments.map substitution.apply)
        (by simpa [signaturesEq] using cataloged)
        (by simpa using arity) ?_
    }
    apply typesWellScoped_of_each_admissible_within
    · intro argument member
      rcases List.mem_map.mp member with ⟨sourceArgument, sourceMember, rfl⟩
      exact argumentsInduction sourceArgument sourceMember
    · intro argument member metavariable occurs
      rw [mem_freeVariables_nominal_iff_recursive]
      exact ⟨argument, member, occurs⟩
  · intro contract arguments cataloged arity _ argumentsInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    refine {
      binders
      typeWellScoped := .contractNominal contract
        (arguments.map substitution.apply)
        (by simpa [signaturesEq] using cataloged)
        (by simpa using arity) ?_
    }
    apply typesWellScoped_of_each_admissible_within
    · intro argument member
      rcases List.mem_map.mp member with ⟨sourceArgument, sourceMember, rfl⟩
      exact argumentsInduction sourceArgument sourceMember
    · intro argument member metavariable occurs
      rw [mem_freeVariables_nominal_iff_recursive]
      exact ⟨argument, member, occurs⟩
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
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact headInduction
    · exact tailInduction current tailMember

/-- `Coerce` profile instantiation commutes with an inference substitution
when both the raw and normalized profile are interpreted in the same active
semantic context.  Catalog membership is unchanged, so no source-to-target
context closure is needed. -/
theorem coercionProfileInstantiates_apply_in_active
    {substitution : Substitution} {active : SourceSemantics.Context}
    {sourceType targetType : Ty} {primary : ProgramPredicate}
    {methodPredicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (profile : CoercionProfileInstantiates active sourceType targetType
      primary methodPredicates) :
    CoercionProfileInstantiates active
      (substitution.apply sourceType) (substitution.apply targetType)
      (TypedTraitResolution.applySubstitution substitution primary)
      (methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  cases profile with
  | @intro signature method fromParameter toParameter signatureMem nameEq
      parametersEq methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter
            (fun candidate => candidate.name == "coerce") := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(fromParameter, sourceType), (toParameter, targetType)]
          signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.parameter_types)
      have returnCompose :=
        FlexibleSubstitution.TypesWellScoped.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            methodWellFormed.return_types)
      have predicateCompose :=
        FlexibleSubstitution.PredicatesWellFormed.applyFlexible_composeParameters
          (context := signatureContext active.signatures signature.id
            signature.parameters
            (signature.wherePredicates ++ method.wherePredicates))
          substitution
          [(fromParameter, sourceType), (toParameter, targetType)] innerExact
          methodWellFormed.predicates
      change CoercionProfileInstantiates active
        (substitution.apply sourceType) (substitution.apply targetType)
        { trait := .declaration signature.id
          subject := substitution.apply sourceType
          arguments := [substitution.apply targetType] }
        ((method.wherePredicates.map
          (ProgramPredicate.applyParameters
            [(fromParameter, sourceType), (toParameter, targetType)])).map
              (TypedTraitResolution.applySubstitution substitution))
      rw [predicateCompose]
      exact .intro signatureMem nameEq parametersEq methodUnique
        (by
          change method.parameterTypes.map
              (FlexibleSubstitution.ParameterSubstitution.mapRange substitution
                [(fromParameter, sourceType),
                  (toParameter, targetType)]).apply =
            [substitution.apply sourceType]
          rw [← parameterCompose, parameterTypesEq]
          rfl)
        (by
          change method.returnTypes.map
              (FlexibleSubstitution.ParameterSubstitution.mapRange substitution
                [(fromParameter, sourceType),
                  (toParameter, targetType)]).apply =
            [substitution.apply targetType]
          rw [← returnCompose, returnTypesEq]
          rfl)

/-- One planned coercion edge remains a valid `Coerce` profile after the
whole-body substitution is applied, interpreted directly in the active
context. -/
theorem plannedCoercionStep_profileInstantiatesAfterSubstitution_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {active : SourceSemantics.Context} {substitution : Substitution}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {planned : Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (consistent :
      Detail.PlannedCoercionStep.ProfileConsistent trait profile planned) :
    CoercionProfileInstantiates active
      (substitution.apply planned.source)
      (substitution.apply planned.target)
      (TypedTraitResolution.applySubstitution substitution planned.predicate)
      (planned.methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  have raw : CoercionProfileInstantiates active planned.source planned.target
      planned.predicate planned.methodPredicates := by
    simpa [consistent.predicate_eq] using
      coercionMethodProfile?_some_instantiates signaturesEq traitName
        profileSuccess consistent.methodPredicates_eq
  exact coercionProfileInstantiates_apply_in_active catalog raw

private theorem committed_member_has_planned_correspondence_in_active
    {requirements : List Requirement}
    {plan : List Detail.PlannedCoercionStep}
    {steps : List CoercionStep}
    (corresponds : Detail.CoercionPlanCommitCorresponds requirements
      plan steps)
    {committed : CoercionStep}
    (member : committed ∈ steps) :
    ∃ planned, planned ∈ plan ∧
      Detail.PlannedCoercionStep.CommitCorresponds requirements
        planned committed := by
  induction corresponds with
  | nil => simp at member
  | @cons planned committed plan steps head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨planned, by simp, head⟩
      · obtain ⟨candidate, candidateMember, candidateCorresponds⟩ :=
          induction member
        exact ⟨candidate, by simp [candidateMember], candidateCorresponds⟩

/-- A later whole-body substitution closes a committed coercion plan using
occurrence-scoped evidence, with all profile semantics interpreted directly
in the current active context. -/
theorem coercionPlan?_some_committedPathValid_at_scoped_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {source target : Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (planSuccess :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (requirementsSubset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id,
      id ∈ coercionRequirementIds
        (Detail.commitCoercionPlan state plan).1 →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono
      requirementsSubset
  have retainedStructural : Frontend.SourceInference.CoercionPath.isValid
      source target (Detail.commitCoercionPlan state plan).1 = true :=
    corresponds.isValid (Detail.coercionPlan?_some_isValid planSuccess)
  have normalizedStructural : Frontend.SourceInference.CoercionPath.isValid
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) = true :=
    Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution retainedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨committed, committedMember, rfl⟩ := List.mem_map.mp stepMember
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence_in_active corresponds
      committedMember
  have consistent := Detail.coercionPlan?_some_profileConsistent
    traitSuccess profileSuccess planSuccess planned plannedMember
  have methodPredicatesEq :
      planned.methodPredicates.map (Detail.applyPredicate later) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate _
    rfl
  have profileInstantiates :=
    plannedCoercionStep_profileInstantiatesAfterSubstitution_in_active
      (substitution := later.inference.substitution) catalog signaturesEq
      traitName profileSuccess consistent
  have normalizedProfile : CoercionProfileInstantiates active
      (later.resolve planned.source) (later.resolve planned.target)
      (Detail.applyPredicate later planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate later)) := by
    rw [methodPredicatesEq]
    simpa [State.resolve, TypeSystem.InferState.resolve,
      Detail.applyPredicate] using profileInstantiates
  apply committedCoercionStepValidAt (state := later) correspondence
    normalizedProfile solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered
  intro id member
  apply occurs id
  unfold coercionRequirementIds
  exact List.mem_flatMap.mpr ⟨committed, committedMember, member⟩

/-- Expected-type fitting has a valid normalized output path in the active
context, using only the final scoped ledger and catalog. -/
theorem withExpected_success_coercionPathValid_scoped_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {state later : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id, id ∈ coercionRequirementIds result.coercions →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid active
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercionsEq, _, typeEq⟩ |
      ⟨expectedType, plan, _, planSuccess, resultEq⟩
  · rw [coercionsEq]
    simp only [List.map_nil]
    rw [typeEq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid active
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_at_scoped_in_active
      traitSuccess profileSuccess planSuccess requirementsSubset catalog
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs

/-- Ordinary expression recording closes directly in the active context.
This is the context-stable replacement for the older recorder bridge whose
only use of a parallel raw context was transport of the `Coerce` profile. -/
theorem
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
    {inferenceContext : Frontend.SourceInference.Context}
    {solverContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {rawType : Ty} {form : ExpressionForm}
    {owned : List RequirementId} {expected : Option Ty}
    {state later : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      rawType form owned expected state localSchemeInstantiationStart =
        .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (formType : ExpressionFormHasRawType semanticSource active
      (form.applySubstitution later.inference.substitution)
      (later.inference.substitution.apply rawType) (.ordinary owned))
    (rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply rawType))
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (catalog : SignatureCatalogWellFormed active.signatures)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  obtain ⟨fitted, fittedSuccess, resultExpressionEq, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have recordedContains : ContainsExpression
      (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := source.span
        type := result.1.type
        form
        requirements := owned ++
          Detail.coercionRequirements fitted.coercions
        coercions := fitted.coercions
        localSchemeInstantiationStart
      } := by
    rw [resultExpressionEq, resultStateEq]
    exact recordNode_containsExpression fitted.state _ roots
  have fittedRequirementsSubset :
      fitted.state.requirements ⊆ later.requirements := by
    intro requirement member
    apply requirementsSubset
    rw [resultStateEq]
    exact member
  have fittedSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        fitted.state.inference.substitution := by
    simpa [resultStateEq, State.recordNode] using substitutionExtends
  have occursOwned : ∀ requirement, requirement ∈ owned →
      PrimaryRequirementOccursAt evidenceSource
        (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have occursCoercion : ∀ requirement,
      requirement ∈ coercionRequirementIds fitted.coercions →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      owned ++ Detail.coercionRequirements fitted.coercions
    apply List.mem_append_right owned
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have ownedValid : RequirementIdsValid active owned :=
    ledger.requirementIdsValidAt ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered occursOwned
  have path :=
    withExpected_success_coercionPathValid_scoped_in_active
      fittedSuccess traitSuccess profileSuccess fittedRequirementsSubset
      catalog signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      occursCoercion
  have rawEndpointEq :
      later.inference.substitution.apply (fitted.state.resolve rawType) =
        later.inference.substitution.apply rawType :=
    TypeSystem.InferState.apply_resolve_eq_apply fittedSubstitutionExtends
      rawType
  have finalPath : CoercionPathValid active
      (later.inference.substitution.apply rawType)
      (later.inference.substitution.apply result.1.type)
      (fitted.coercions.map
        (CoercionStep.applySubstitution
          later.inference.substitution)) := by
    rw [resultExpressionEq, ← rawEndpointEq]
    exact path
  have requirementsEq :
      owned ++ Detail.coercionRequirements fitted.coercions =
      owned ++ coercionRequirementIds
        (fitted.coercions.map
          (CoercionStep.applySubstitution
            later.inference.substitution)) := by
    rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    rfl
  refine ExpressionTypingBase.intro (plan := .ordinary owned)
    recordedContains (by rfl) ?_ rawAdmissible ?_
  · simpa [ExpressionNode.applySubstitution] using formType
  · exact ExpressionRequirementPlan.Valid.ordinary ownedValid finalPath
      requirementsEq

/-- The local-reference requirement spine needs only semantic substitution
extension from its allocation state to the whole solver state.  Allocator
growth and final-state `next` bounds are irrelevant to the normalized
predicate equality used by declarative evidence. -/
theorem localReferenceRequirementSequenceProves_afterSemanticExtension
    {solverContext : Frontend.SourceInference.Context}
    {instantiationState finalState : State}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {source : TypedSource} {occurrence : NodeId}
    {binder : TypedBinder} {instantiationStart : Nat}
    {ids : List RequirementId}
    (extension : finalState.inference.substitution.SemanticallyExtends
      instantiationState.inference.substitution)
    (corresponds : RequirementPredicatesCorrespond finalState.requirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (Detail.applyPredicate instantiationState)) ids)
    (success : Detail.solveRequirements solverContext finalState
      finalState.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base source)
    (ownership : RequirementOwnership base source)
    (signaturesEq : active.signatures = base.signatures)
    (requirementsEq : active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered source active occurrence)
    (occurs : ∀ id, id ∈ ids →
      PrimaryRequirementOccursAt source occurrence id) :
    RequirementSequenceProves active ids
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (TypedTraitResolution.applySubstitution
          finalState.inference.substitution)) := by
  have proves := solveRequirements_correspondingSequenceProvesAt corresponds
    success solvedEq ledger ownership signaturesEq requirementsEq
    assumptionsMono covered occurs
  simpa only [List.map_map, Function.comp_def, Detail.applyPredicate,
    TypedTraitResolution.applySubstitution_semanticallyExtends extension] using
      proves

/-- Whole-body finalization supplies an admissible range for its returned
substitution in every active context with the declaration's static scope. -/
theorem FinalInferenceResources.substitutionRangeAdmissible
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {active : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    SubstitutionRangeAdmissible active finalized.substitution :=
  InferenceSubstitutionRangeFormationValidated.rangeAdmissible
    resources.range_formation binders signaturesEq parametersEq ownerEq
      residual

/-- A retained expression node has an admissible finalized type in the
current active context without a fixed source-side context-substitution
certificate. -/
theorem FinalInferenceResources.expressionTypeAdmissible_in_active
    {wholeContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {node : ExpressionNode}
    (member : Node.expression node ∈
      (evidenceState.toTypedSource roots).nodes)
    {active : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = wholeContext.signatures)
    (parametersEq : active.typeParameters = wholeContext.typeParameters)
    (ownerEq : active.currentDeclaration =
      some wholeContext.scope.genericOwner)
    (residual : active.residualTypeVariables = true) :
    TypeAdmissible active (finalized.substitution.apply node.type) :=
  inferenceTypeFormationValidated_apply_typeAdmissible
    (resources.expressionTypeFormationValidated member)
    resources.range_formation binders signaturesEq parametersEq ownerEq
      residual

/-- The state/context facts shared by every recursive expression boundary.
Unlike `RecursiveStatementInvariant`, this record has no ambient return type:
expression inference preserves the active lexical context and needs only the
whole-finalization scope, allocator bounds, and final-substitution extension. -/
structure RecursiveExpressionInvariant
    (wholeContext : Frontend.SourceInference.Context)
    (finalized : Frontend.SourceInference.Result)
    (state : State) (semanticContext : SourceSemantics.Context) : Prop where
  active : ActiveLocalContextInvariant state finalized.substitution
    semanticContext
  ready : state.InferenceReady
  bindersBelow : state.LocalBindersBelowNextLocal
  nodesBelow : state.NodesBelowNextOccurrence
  schemeIsolation : ActiveSchemeQuantifierIsolation state
  substitutionExtension : finalized.substitution.SemanticallyExtends
    state.inference.substitution
  signaturesEq : semanticContext.signatures =
    (finalizedRequirementContext wholeContext finalized).signatures
  typeParametersEq : semanticContext.typeParameters =
    wholeContext.typeParameters
  declarationEq : semanticContext.currentDeclaration =
    some wholeContext.scope.genericOwner
  residual : semanticContext.residualTypeVariables = true
  solvedRequirementsEq : semanticContext.solvedRequirements =
    (finalizedRequirementContext wholeContext finalized).solvedRequirements
  assumptionsMono :
    (finalizedRequirementContext wholeContext finalized).assumptions ⊆
      semanticContext.assumptions

/-- Reserving an expression occurrence preserves every recursive expression
invariant, including the lexical quantifier-isolation certificate. -/
theorem RecursiveExpressionInvariant.allocateExpressionId
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial allocated : State} {id : ExpressionId}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext)
    (allocationEq : initial.allocateExpressionId = (id, allocated)) :
    RecursiveExpressionInvariant wholeContext finalized allocated
      semanticContext := by
  have allocatedEq : initial.allocateExpressionId.2 = allocated :=
    congrArg Prod.snd allocationEq
  subst allocated
  refine {
    active := invariant.active.congr_localBinders (by rfl)
    ready := State.InferenceReady.allocateExpressionId invariant.ready
    bindersBelow :=
      State.allocateExpressionId_preserves_localBindersBelowNextLocal initial
        invariant.bindersBelow
    nodesBelow :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        invariant.nodesBelow
    schemeIsolation :=
      activeSchemeQuantifierIsolation_allocateExpressionId
        invariant.schemeIsolation allocationEq
    substitutionExtension := invariant.substitutionExtension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }

/-- Forget the statement-only return bound from the mutual statement
invariant at an expression child boundary. -/
theorem RecursiveExpressionInvariant.ofStatement
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty} {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized state semanticContext) :
    RecursiveExpressionInvariant wholeContext finalized state
      semanticContext := {
  active := invariant.active
  ready := invariant.ready
  bindersBelow := invariant.bindersBelow
  nodesBelow := invariant.nodesBelow
  schemeIsolation := invariant.schemeIsolation
  substitutionExtension := invariant.substitutionExtension
  signaturesEq := invariant.signaturesEq
  typeParametersEq := invariant.typeParametersEq
  declarationEq := invariant.declarationEq
  residual := invariant.residual
  solvedRequirementsEq := invariant.solvedRequirementsEq
  assumptionsMono := invariant.assumptionsMono
}

theorem RecursiveExpressionInvariant.signatures_eq_whole
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state
      semanticContext) :
    semanticContext.signatures = wholeContext.signatures := by
  simpa [finalizedRequirementContext, Context.withSolvedRequirements,
    Context.withAssumptions, Context.ofSignatures] using
      invariant.signaturesEq

theorem RecursiveExpressionInvariant.typeParameterBinders
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {state : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state
      semanticContext)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters) :
    TypeParameterBindersWellFormed semanticContext := by
  let declarationScope := declarationContext wholeContext.signatures
    wholeContext.scope.genericOwner wholeContext.typeParameters [] []
  have declarationBinders : TypeParameterBindersWellFormed
      declarationScope := by
    exact
      Solcore.SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        canonical [] []
  exact StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    (source := declarationScope) (target := semanticContext)
    (by
      simpa [declarationScope, declarationContext, signatureContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration,
        Context.ofSignatures] using
          invariant.typeParametersEq)
    (by
      simpa [declarationScope, declarationContext, signatureContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration,
        Context.ofSignatures] using
          invariant.declarationEq)
    declarationBinders

/-- The numeric-literal branch closes directly in the active recursive
context.  This version uses finalization's validated literal ledger and the
context-stable ordinary recorder bridge, so it does not require a parallel
unsubstituted semantic context. -/
theorem
    inferExprFuel_success_numericLiteral_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {source : Syntax.CoreLiteralValue}
    {rawValue : Nat} {expected : Option Ty}
    {initial allocated : State} {id : ExpressionId}
    {inferred : InferredExpression} {resultState : State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource}
    {active : SourceSemantics.Context}
    (expressionEq : expression.value = .literal literal)
    (literalEq : literal.value = source)
    (decoded : Frontend.numericLiteralValue? source = some rawValue)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (integerLiteralsSubset : resultState.integerLiterals ⊆
      evidenceState.integerLiterals)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let rawType := allocated.fresh.1
  let freshState := allocated.fresh.2
  let addition := freshState.addRequirementWithId
    (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩
    expression := id
    requirement := addition.1
  }
  let literalState : State := {
    addition.2 with
    integerLiterals := addition.2.integerLiterals ++ [origin]
  }
  let resolution : IntegerLiteralResolution := {
    rawValue
    targetType := rawType
    requirement := addition.1
  }
  obtain ⟨recorded, originMember, requirementMember⟩ :=
    Detail.inferExprFuel_success_numericLiteral_record expressionEq literalEq
      decoded allocationEq success
  have originMemberFinal : origin ∈ evidenceState.integerLiterals :=
    integerLiteralsSubset originMember
  have requirementMemberFinal :
      ({ id := origin.requirement
         predicate := ProgramSignatures.builtinIntPredicate
           (.variable origin.metavariable) } : Requirement) ∈
        evidenceState.requirements := by
    apply requirementsSubset
    simpa [origin, addition, freshState, rawType,
      State.fresh, TypeSystem.InferState.fresh] using requirementMember
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : PrimaryRequirementOccursAt finalized.typedSource
      (.expression inferred.id) resolution.requirement := by
    apply retained recordedContains
    change resolution.requirement ∈
      [addition.1] ++ Detail.coercionRequirements coercions
    simp [resolution]
  have literalValid : IntegerLiteralValid active source
      (resolution.applySubstitution finalized.substitution) := by
    apply resources.integerLiteralValidAt
      (origin := origin) (decoded := by simpa [resolution] using decoded)
    · simp [resolution, origin, rawType, State.fresh,
        TypeSystem.InferState.fresh]
    · rfl
    · exact originMemberFinal
    · exact requirementMemberFinal
    · exact invariant.signaturesEq
    · exact invariant.solvedRequirementsEq
    · exact invariant.assumptionsMono
    · exact covered
    · exact occurs
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.integerLiteral source resolution).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply rawType) (.ordinary [addition.1]) := by
    simpa [ExpressionForm.applySubstitution, resolution,
      IntegerLiteralResolution.applySubstitution] using
        (ExpressionFormHasRawType.integerLiteral literalValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply rawType) := by
    simpa [resolution, IntegerLiteralResolution.applySubstitution] using
      literalValid.target_type_admissible
        (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        resultState.inference.substitution := by
    simpa only [finalSubstitutionEq] using resultSubstitutionExtension
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded finalSubstitutionExtends requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- The builtin-Boolean identifier is source-independent; only its optional
output coercion consults the whole finalized ledger. -/
theorem
    inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (isBoolean :
      (name.value == "true" || name.value == "false") = true)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id .bool
      (.reference name.value (.builtinBoolean (name.value == "true"))) []
      expected allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinBooleanIdentifier_record expressionEq
      allocationEq lookupEq isBoolean success
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinBoolean (name.value == "true"))).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply .bool) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinBoolean (context := active)
          (name.value == "true")))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply .bool) := by
    simpa using TypeAdmissible.bool
      (invariant.typeParameterBinders canonical)
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A builtin-function identifier has a closed, catalog-independent raw
reference type in the active context. -/
theorem
    inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {function : BuiltinFunctionId} {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value =
      .ok [])
    (builtinEq : Frontend.builtinFunctionNamed? name.value = some function)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id function.type
      (.reference name.value (.builtinFunction function)) [] expected
      allocated = .ok (inferred, resultState) :=
    Detail.inferExprFuel_success_builtinFunctionIdentifier_record expressionEq
      allocationEq lookupEq notBoolean functionsEq builtinEq success
  have fixedType : finalized.substitution.apply function.type =
      function.type := by
    cases function <;>
      simp [BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes,
        BuiltinFunctionId.returnType, Ty.productMany]
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinFunction function)).applySubstitution
          finalized.substitution)
      (finalized.substitution.apply function.type) (.ordinary []) := by
    rw [fixedType]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
      (ExpressionFormHasRawType.reference (source := semanticSource)
        (ReferenceUseValid.builtinFunction (context := active) function))
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply function.type) := by
    rw [fixedType]
    exact TypeAdmissible.builtinFunction
      (invariant.typeParameterBinders canonical) function
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- Canonical local-scheme instantiation closes directly in the active
recursive context.  The allocation and no-capture certificates remain
explicit because they are supplied by the recursive ledger/provenance
invariants rather than by a fixed source-side substitution context. -/
theorem
    inferExprFuel_success_localIdentifier_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (certificate :
      let instantiationStart := allocated.inference.next
      let instantiated :=
        binder.scheme.instantiateWithSubstitution instantiationStart
      let inference := { allocated.inference with next := instantiated.next }
      let advanced : State := { allocated with inference }
      let predicates := binder.schemeRequirements.map fun requirement =>
        Detail.applyPredicate advanced
          (TypedTraitResolution.applySubstitution instantiated.substitution
            requirement.predicate)
      State.LookupBinderRequirementAllocationCertificate advanced binder
        predicates)
    (noCapture : Detail.LocalBinderInstantiationNoCapture
      finalized.substitution binder)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  let instantiationStart := allocated.inference.next
  let instantiated :=
    binder.scheme.instantiateWithSubstitution instantiationStart
  let inference := { allocated.inference with next := instantiated.next }
  let advanced : State := { allocated with inference }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution
        requirement.predicate)
  let allocation := advanced.addRequirementsWithIds predicates
  change State.LookupBinderRequirementAllocationCertificate advanced binder
    predicates at certificate
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id (advanced.resolve instantiated.body)
      (.reference name.value (.local binder.id)) allocation.1 expected
      allocation.2
      (localSchemeInstantiationStart := some instantiationStart) =
        .ok (inferred, resultState) := by
    simpa only [instantiationStart, instantiated, inference, advanced,
      predicates, allocation] using
        (Detail.inferExprFuel_success_localIdentifier_record expressionEq
          allocationEq lookupEq success)
  have branchFacts := inferExprFuel_success_localIdentifier_facts
    expressionEq allocationEq lookupEq success certificate roots
  change ∃ coercions,
      ContainsExpression (resultState.toTypedSource roots) inferred.id {
        id := inferred.id
        span := expression.span
        type := inferred.type
        form := .reference name.value (.local binder.id)
        requirements := allocation.1 ++
          Detail.coercionRequirements coercions
        coercions
        localSchemeInstantiationStart := some instantiationStart
      } ∧
      allocation.1.Nodup ∧
      (∀ requirement, requirement ∈ allocation.1 →
        requirement ∉ localSchemeTemplateIds binder) ∧
      RequirementPredicatesCorrespond resultState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1
    at branchFacts
  obtain ⟨coercions, recordedContains, actualUnique, actualDisjoint,
      resultCorresponds⟩ := branchFacts
  have evidenceCorresponds :
      RequirementPredicatesCorrespond evidenceState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 :=
    resultCorresponds.mono requirementsSubset
  have finalCorresponds :
      RequirementPredicatesCorrespond resources.finalState.requirements
        ((instantiateLocalSchemePredicates instantiated.substitution
          binder).map (Detail.applyPredicate advanced)) allocation.1 := by
    rw [resources.requirements_eq]
    exact evidenceCorresponds
  have occurs : ∀ requirement, requirement ∈ allocation.1 →
      PrimaryRequirementOccursAt finalized.typedSource
        (.expression inferred.id) requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      allocation.1 ++ Detail.coercionRequirements coercions
    exact List.mem_append_left _ member
  have allocationInferenceEq : allocated.inference = initial.inference := by
    have projection := congrArg
      (fun pair : ExpressionId × State => pair.2.inference) allocationEq
    change initial.inference = allocated.inference at projection
    exact projection.symm
  have finalExtendsAdvanced :
      finalized.substitution.SemanticallyExtends
        advanced.inference.substitution := by
    simpa [advanced, inference, allocationInferenceEq] using
      invariant.substitutionExtension
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirements :=
    localReferenceRequirementSequenceProves_afterSemanticExtension
      (finalState := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      (active := active) (source := finalized.typedSource)
      (occurrence := .expression inferred.id)
      (by simpa only [finalSubstitutionEq] using finalExtendsAdvanced)
      finalCorresponds resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered occurs
  have allocatedInvariant :=
    (invariant.allocateExpressionId allocationEq).active
  have environment := localReferenceEnvironmentFacts_of_lookupBinder?
    allocatedInvariant.aligned allocatedInvariant.formation lookupEq
  have appliedDisjoint : ∀ requirement,
      requirement ∈ allocation.1 →
        requirement ∉
          localSchemeTemplateIds
            (binder.applySubstitution finalized.substitution) := by
    simpa only
      [FlexibleSubstitution.localSchemeTemplateIds_applySubstitution] using
        actualDisjoint
  have binders := invariant.typeParameterBinders canonical
  have range := resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq
    invariant.declarationEq invariant.residual
  have instantiationValid :=
    canonicalLocalSchemeInstantiationValid_afterSubstitution binders
      invariant.residual range environment.2.2.2 environment.2.2.1
      noCapture instantiationStart actualUnique appliedDisjoint
      (by simpa only [finalSubstitutionEq] using requirements)
  have referenceValid : ReferenceUseValid active (.local binder.id)
      (finalized.substitution.apply instantiated.body) allocation.1 := by
    simpa only [FlexibleSubstitution.applyTypedBinder_id] using
      (ReferenceUseValid.local environment.1 environment.2.1
        instantiationValid)
  have rawEndpointEq :
      finalized.substitution.apply
          (advanced.resolve instantiated.body) =
        finalized.substitution.apply instantiated.body := by
    simpa [State.resolve, TypeSystem.InferState.resolve] using
      finalExtendsAdvanced instantiated.body
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value (.local binder.id)
        ).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (advanced.resolve instantiated.body))
      (.ordinary allocation.1) := by
    rw [rawEndpointEq]
    simpa [ExpressionForm.applySubstitution,
      ReferenceResolution.applySubstitution] using
        (ExpressionFormHasRawType.reference (source := semanticSource)
          referenceValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply
        (advanced.resolve instantiated.body)) := by
    rw [rawEndpointEq]
    exact instantiationValid.type_admissible
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- A resolved proxy annotation is rigidly formed and therefore fixed by the
whole inference substitution.  Its branch closes in the active recursive
context without a source-side context-closure certificate. -/
theorem inferExprFuel_success_proxy_expressionTypingBase_retained_in_active
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    {fuel : Nat} {expression : Syntax.Expr} {marker : Syntax.SourceSpan}
    {sourceType : Syntax.TypeExpr} {expected : Option Ty}
    {initial allocated resultState : State} {id : ExpressionId}
    {inferred : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .proxy marker sourceType)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (fun row => row.name) =
        some "Coerce")
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  obtain ⟨inner, resolution, recorded⟩ :=
    Detail.inferExprFuel_success_proxy_facts expressionEq allocationEq success
  have canonicalInference : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters := by
    simpa [ownerEq, parametersEq] using canonical
  have activeSignaturesEq : active.signatures =
      inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeParametersEq : active.typeParameters =
      inferenceContext.typeParameters :=
    invariant.typeParametersEq.trans parametersEq.symm
  have activeOwnerEq : active.currentDeclaration =
      some inferenceContext.scope.genericOwner := by
    simpa [ownerEq] using invariant.declarationEq
  have innerWellFormed : TypeWellFormed active inner :=
    resolveSourceType_success_typeWellFormed canonicalInference
      activeSignaturesEq activeParametersEq activeOwnerEq resolution
  have fixedInner : finalized.substitution.apply inner = inner :=
    Detail.resolveSourceType_success_apply_eq_self finalized.substitution
      resolution
  have innerAdmissible : TypeAdmissible active
      (finalized.substitution.apply inner) := by
    rw [fixedInner]
    exact TypeAdmissible.ofWellFormed innerWellFormed
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.proxy inner).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (.proxy inner)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, fixedInner] using
      ExpressionFormHasRawType.proxy innerAdmissible
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply (.proxy inner)) := by
    simpa [fixedInner] using TypeAdmissible.proxy innerAdmissible
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have requirementsSubsetFinal : resultState.requirements ⊆
      resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirementsSubset member
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_in_active
      (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      recorded
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      traitSuccess profileSuccess activeCatalog activeSignaturesEq traitName
      resources.solve_success resources.solved_context_eq resources.ledger
      resources.ownership invariant.signaturesEq
      invariant.solvedRequirementsEq invariant.assumptionsMono covered)

/-- Strong recursive expression obligation.  Its conclusion is intentionally
an `ExpressionTypingBase`: a selected enclosing call/operator may rewrite a
child root's authoritative type while retaining its form, requirements, and
direct children.  Closing the base to `ExpressionHasType` is reserved for the
local-source wrapper below, where exact source extension is available. -/
def InferExprFuelRetainedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
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
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    TypingSourceExtends semanticSource finalized.typedSource →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred

/-- Statement-facing local-source expression theorem.  The raw result source
is an exact prefix of the whole evidence state for statement children; the
substituted result is an exact prefix of `semanticSource`, so the retained
base can be closed to ordinary declarative expression typing there. -/
def InferExprFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferExprFuel fuel inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
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
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type)

/-- Exact local-source typing is the closure of retained recursive soundness.
This theorem is the stable bridge consumed by statement branches. -/
theorem inferExprFuelScopedSoundness_of_retainedSoundness
    {fuel : Nat}
    (retainedSound : InferExprFuelRetainedSoundness fuel) :
    InferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    semanticContext success resources resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant expectedBelow
    resultExtension semanticExtension rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered
  have resultToFinal : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource :=
    TypingSourceExtends.trans resultExtension semanticExtension
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have base := retainedSound success resources resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant expectedBelow semanticExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    requirementsRetained childrenRetained covered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible
      requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawExtension.nodes_prefix.subset contains.1
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      exact
        (ExpressionTypingBase.intro contains typeEq formType rawAdmissible
          requirements).expressionHasType
          (ExpressionNodesPreservedAt.ofTypingSourceExtends resultExtension)
          finalAdmissible

end Solcore.SourceSemantics.SourceInferenceSoundness
