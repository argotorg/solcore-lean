import Solcore.Frontend.SourceInference.ProgramProperties
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.TraitResolutionSoundness

/-! Conditional bridge from executable finalization to declarative typing. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference

private theorem trait?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {signature : ProgramTraitSignature}
    (found : signatures.trait? id = some signature) :
    signature ∈ signatures.traits ∧ signature.id = id := by
  have rawFound : signatures.traits.find?
      (fun candidate => decide (candidate.id = id)) = some signature := by
    simpa [ProgramSignatures.trait?] using found
  have accepted : decide (signature.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramTraitSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem list_eq_pair_of_length_eq_two
    {value : Type} {values : List value}
    (length_eq : values.length = 2) :
    ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at length_eq
  | cons first rest =>
      cases rest with
      | nil => simp at length_eq
      | cons second tail =>
          cases tail with
          | nil => exact ⟨first, second, rfl⟩
          | cons third tail => simp at length_eq

/-- A successfully loaded coercion-method profile and its successfully
instantiated predicate row supply the declarative `Coerce` profile used by
source typing.  The explicit name premise isolates the remaining
environment-to-signature catalog alignment obligation; independently assembled
inference contexts are not otherwise required to keep those names aligned. -/
theorem coercionMethodProfile?_some_instantiates
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {source target : TypeSystem.Ty}
    {methodPredicates : List ProgramPredicate}
    (signatures_eq :
      semanticContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (predicates_success :
      Detail.coercionMethodPredicates (some profile) source target =
        .ok methodPredicates) :
    CoercionProfileInstantiates semanticContext source target {
      trait := .declaration trait
      subject := source
      arguments := [target]
    } methodPredicates := by
  cases signature_lookup : inferenceContext.signatures.trait? trait with
  | none =>
      simp [signature_lookup] at trait_name
  | some signature =>
      have signature_name : signature.name = "Coerce" := by
        simpa [signature_lookup] using trait_name
      have signature_facts := trait?_eq_some_facts signature_lookup
      simp only [Detail.coercionMethodProfile?, signature_lookup, pure,
        Pure.pure, Except.pure, bind, Except.bind] at profile_success
      by_cases arity : signature.parameters.length = 2
      · rw [if_pos arity] at profile_success
        obtain ⟨fromParameter, toParameter, parameters_eq⟩ :=
          list_eq_pair_of_length_eq_two arity
        cases methods_eq : signature.methods.filter
            (fun candidate => candidate.name == "coerce") with
        | nil =>
            rw [methods_eq] at profile_success
            simp at profile_success
        | cons method rest =>
            cases rest with
            | nil =>
                rw [methods_eq] at profile_success
                simp only [Except.ok.injEq, Option.some.injEq] at profile_success
                subst profile
                by_cases parameter_types_eq :
                    method.parameterTypes.map
                        (TypeSystem.ParameterSubstitution.apply
                          [(fromParameter, source), (toParameter, target)]) =
                      [source]
                · by_cases return_types_eq :
                      method.returnTypes.map
                          (TypeSystem.ParameterSubstitution.apply
                            [(fromParameter, source), (toParameter, target)]) =
                        [target]
                  · have predicate_eq :
                        method.wherePredicates.map
                            (ProgramPredicate.applyParameters
                              [(fromParameter, source),
                                (toParameter, target)]) =
                          methodPredicates := by
                      simpa [Detail.coercionMethodPredicates, parameters_eq,
                        parameter_types_eq, return_types_eq] using
                          predicates_success
                    rw [← signature_facts.2, ← predicate_eq]
                    exact .intro
                      (by rw [signatures_eq]; exact signature_facts.1)
                      signature_name parameters_eq methods_eq
                      parameter_types_eq return_types_eq
                  · simp [Detail.coercionMethodPredicates, parameters_eq,
                      parameter_types_eq, return_types_eq, bind, Except.bind]
                      at predicates_success
                · simp [Detail.coercionMethodPredicates, parameters_eq,
                    parameter_types_eq, bind, Except.bind]
                    at predicates_success
            | cons second tail =>
                rw [methods_eq] at profile_success
                simp at profile_success
      · rw [if_neg arity] at profile_success
        simp at profile_success

/-- A profile-consistent planned coercion edge remains a declaratively valid
`Coerce` profile after the ambient inference substitution closes its endpoint
types and ordered method predicates. -/
theorem plannedCoercionStep_profileInstantiatesAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {planned : Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (consistent :
      Detail.PlannedCoercionStep.ProfileConsistent trait profile planned) :
    CoercionProfileInstantiates targetContext
      (substitution.apply planned.source)
      (substitution.apply planned.target)
      (TypedTraitResolution.applySubstitution substitution planned.predicate)
      (planned.methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  have raw : CoercionProfileInstantiates sourceContext planned.source
      planned.target planned.predicate planned.methodPredicates := by
    simpa [consistent.predicate_eq] using
      coercionMethodProfile?_some_instantiates signatures_eq trait_name
        profile_success consistent.methodPredicates_eq
  exact FlexibleSubstitution.CoercionProfileInstantiates.applySubstitution
    catalog contextValid raw

/-- A successful executable candidate check retains a declaratively
admissible occurrence of the candidate signature.  Argument fitting,
expected-type fitting, predicate validation, and ledger allocation happen
after the canonical fresh generic instantiation and cannot replace it. -/
theorem tryFunctionCandidate_instantiationAdmissible
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationInstantiation.Admissible semanticContext
      result.instantiation := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  exact DeclarationInstantiation.ofInstantiated_admissible catalog binders
    residual member state.inference.next

/-- The retained candidate instantiation also supplies the exact declarative
application profile needed by the direct-call typing rule.  Its parameter row
and result are the catalog projections under the one shared fresh rigid
substitution; later argument/result fitting is deliberately outside this raw
application fact. -/
theorem tryFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationApplicationValid semanticContext result.instantiation
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          (signature.scheme.instantiate
            state.inference.next).parameterSubstitution))
      ((signature.scheme.instantiate state.inference.next)
        |>.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes))
      (signature.scheme.instantiate state.inference.next).predicates := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  let instantiated := signature.scheme.instantiate state.inference.next
  refine .intro member
    (DeclarationInstantiation.ofInstantiated_admissible catalog binders
      residual member state.inference.next) rfl rfl rfl ?_ rfl
  change instantiated.body = .function
    (TypeSystem.Ty.productMany
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          instantiated.parameterSubstitution)))
    (instantiated.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes))
  rw [Frontend.ConstrainedDeclarationScheme.instantiate_body,
    (catalog.functions_semantic signature member).scheme_body,
    StructuralSubstitution.apply_function,
    StructuralSubstitution.apply_productMany]

/-- A successful overload selection comes from one semantic-catalog member
in the supplied candidate list and retains that member's exact declarative
application profile.  This theorem intentionally forgets ranking optimality;
only origin and static validity are needed by direct-call typing. -/
theorem selectFunctionCandidateFrom_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (candidates_subset : candidates ⊆
      semanticContext.signatures.functions)
    (success : Detail.selectFunctionCandidateFrom inferenceContext name
      candidates arguments integerLiteralOrigins call expected state =
        .ok result) :
    ∃ signature, signature ∈ candidates ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  obtain ⟨signature, member, candidateSuccess⟩ :=
    Detail.selectFunctionCandidateFrom_success_candidate success
  refine ⟨signature, member, ?_⟩
  exact tryFunctionCandidate_declarationApplicationValid catalog binders
    residual (candidates_subset member) candidateSuccess

/-- Ordinary unqualified overload selection inherits the same declarative
application guarantee because successful visible-name lookup returns only
members of the inference catalog.  Catalog equality transports that origin
to the semantic context used by source typing. -/
theorem selectFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (signatures_eq : semanticContext.signatures =
      inferenceContext.signatures)
    (success : Detail.selectFunctionCandidate inferenceContext name arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∃ signature, signature ∈ semanticContext.signatures.functions ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  unfold Detail.selectFunctionCandidate at success
  cases candidatesResult : Detail.functionsNamed inferenceContext name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      have selection : Detail.selectFunctionCandidateFrom inferenceContext
          name candidates arguments integerLiteralOrigins call expected state =
          .ok result := by
        simpa [candidatesResult, bind, Except.bind] using success
      have inferenceSubset :=
        Detail.functionsNamed_success_subset_catalog candidatesResult
      have semanticSubset : candidates ⊆
          semanticContext.signatures.functions := by
        intro signature member
        rw [signatures_eq]
        exact inferenceSubset member
      obtain ⟨signature, member, valid⟩ :=
        selectFunctionCandidateFrom_declarationApplicationValid catalog
          binders residual semanticSubset selection
      exact ⟨signature, semanticSubset member, valid⟩

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) :
    (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indices_eq
    cases left
    cases right
    cases indices_eq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem requirementId_contains_iff_mem
    (id : RequirementId) (ids : List RequirementId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      rw [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, requirementId_beq_iff_eq, induction]

/-- Successful normalized predicate solving retains declaratively valid
evidence.  The available assumptions are normalized exactly once by the same
inference substitution used by the executable solver. -/
theorem solveNormalizedPredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {goal : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solveNormalizedPredicate context state goal =
      .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules goal retained := by
  unfold Detail.solveNormalizedPredicate at success
  cases assumed : Detail.requirementAssumption? context state goal with
  | true =>
      simp only [assumed, ↓reduceIte, Except.ok.injEq] at success
      subst retained
      apply RetainedEvidenceValid.intro (.assumption goal)
      apply EvidenceValid.assumption
      unfold Detail.requirementAssumption? at assumed
      obtain ⟨assumption, member, equal⟩ := List.any_eq_true.mp assumed
      apply List.mem_map.mpr
      exact ⟨assumption, member, of_decide_eq_true equal⟩
  | false =>
      cases resolved : TypedTraitResolution.resolve
          context.signatures.resolutionRules context.traitDepth goal with
      | mk outcome statistics =>
          cases outcome with
          | noSolution =>
              simp [assumed, resolved] at success
          | inconclusive reason =>
              simp [assumed, resolved] at success
          | success evidence =>
              simp [assumed, resolved] at success
              subst retained
              apply RetainedEvidenceValid.weakenAssumptions
                (smaller := [])
              · simp
              · exact
                  TraitResolutionSoundness.resolve_success_retainedEvidenceValid
                    (rules := context.signatures.resolutionRules)
                    (maxDepth := context.traitDepth)
                    (goal := goal)
                    (retained := evidence)
                    (by simp [resolved])

/-- `solvePredicate` first normalizes its source predicate and then delegates
to `solveNormalizedPredicate`, so its successful result has the same retained
evidence guarantee at the normalized goal. -/
theorem solvePredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solvePredicate context state source = .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules
      (Detail.applyPredicate state source) retained := by
  exact solveNormalizedPredicate_sound success

/-- An ordinary solved ledger row inherits the predicate solver's evidence
validity once the executable and declarative contexts agree on the catalog and
on the normalized declaration assumptions. -/
theorem solveRequirementEvidence_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    {semanticContext : SourceSemantics.Context}
    (ordinary : requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirementEvidence inferenceContext state
      requirement = .ok retained) :
    SolvedRequirementValid semanticContext {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := retained
    } := by
  have ordinaryContains :
      state.localSchemeAssumptions.contains requirement.id = false := by
    cases containsEq : state.localSchemeAssumptions.contains requirement.id with
    | false => rfl
    | true =>
        exact False.elim
          (ordinary ((requirementId_contains_iff_mem _ _).mp containsEq))
  have normalizedSuccess :
      Detail.solveNormalizedPredicate inferenceContext state
          (Detail.applyPredicate state requirement.predicate) = .ok retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [ordinaryContains] at success
    simpa using success
  apply SolvedRequirementValid.intro
  rw [signatures_eq, assumptions_eq]
  exact solveNormalizedPredicate_sound normalizedSuccess

/-- Qualified-local template rows bypass trait search and retain exactly an
assumption for their normalized predicate. -/
theorem solveRequirementEvidence_template_eq
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    (template : requirement.id ∈ state.localSchemeAssumptions)
    (success : Detail.solveRequirementEvidence context state requirement =
      .ok retained) :
    retained = .assumption
      (Detail.applyPredicate state requirement.predicate) := by
  have templateContains :
      state.localSchemeAssumptions.contains requirement.id = true := by
    exact (requirementId_contains_iff_mem _ _).mpr template
  have retainedEq :
      (.assumption (Detail.applyPredicate state requirement.predicate) :
        PredicateEvidence) = retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [templateContains] at success
    change Except.ok (.assumption
      (Detail.applyPredicate state requirement.predicate)) =
        Except.ok retained at success
    exact Except.ok.inj success
  exact retainedEq.symm

/-- Successful ledger solving preserves source order and records, for every
output row, its exact input identity, normalized predicate, and evidence-solver
equation. -/
theorem solveRequirements_corresponds
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence context state requirement =
          .ok row.evidence) requirements solved := by
  induction requirements generalizing solved with
  | nil =>
      simp only [Detail.solveRequirements, Except.ok.injEq] at success
      subst solved
      exact .nil
  | cons requirement rest induction =>
      cases evidenceResult :
          Detail.solveRequirementEvidence context state requirement with
      | error error =>
          simp [Detail.solveRequirements, evidenceResult, bind, Except.bind]
            at success
      | ok evidence =>
          cases tailResult : Detail.solveRequirements context state rest with
          | error error =>
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
          | ok tail =>
              let solvedHead : SolvedRequirement := {
                id := requirement.id
                predicate := Detail.applyPredicate state requirement.predicate
                evidence := evidence
              }
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
              subst solved
              exact .cons (by simp [evidenceResult])
                (induction tailResult)

private theorem solved_row_of_requirement_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement =
          .ok row.evidence) requirements solved)
    {requirement : Requirement}
    (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧
      row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | @cons head row tail rows headCorresponds tailCorresponds induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨row, by simp, headCorresponds.1, headCorresponds.2.1⟩
      · obtain ⟨found, foundMember, idEq, predicateEq⟩ := induction member
        exact ⟨found, by simp [foundMember], idEq, predicateEq⟩

/-- A source-ordered predicate/identity correspondence into a successfully
solved final ledger supplies the declarative evidence sequence for exactly
those normalized predicates. -/
theorem solveRequirements_correspondingSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {predicates : List ProgramPredicate}
    {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements predicates ids)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext ids
      (predicates.map (Detail.applyPredicate state)) := by
  have solverCorresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil => exact .nil
  | @cons predicate id predicates ids member tail induction =>
      apply RequirementSequenceProves.cons
      · obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
          solved_row_of_requirement_mem solverCorresponds member
        exact ⟨row, ⟨by simpa [solved_eq] using rowMember, idEq⟩,
          predicateEq, valid row rowMember⟩
      · exact induction

/-- A committed coercion edge inherits the primary and method evidence rows
owned by its planned edge, in the exact order expected by
`CoercionStepValid`. -/
theorem solveRequirements_committedCoercionStepSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext
      (committed.requirement :: committed.methodRequirements)
      (Detail.applyPredicate state planned.predicate ::
        planned.methodPredicates.map (Detail.applyPredicate state)) := by
  apply RequirementSequenceProves.cons
  · have primaryCorresponds : RequirementPredicatesCorrespond requirements
        [planned.predicate] [committed.requirement] :=
      .cons corresponds.primary_mem .nil
    exact (solveRequirements_correspondingSequenceProves primaryCorresponds
      success solved_eq valid).head
  · exact solveRequirements_correspondingSequenceProves
      corresponds.methods success solved_eq valid

/-- Once its normalized profile and solved ledger are valid, a committed
frontend edge is a declaratively valid coercion step after applying the same
inference substitution used to normalize its requirements. -/
theorem committedCoercionStepValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (profile : CoercionProfileInstantiates semanticContext
      (state.resolve planned.source) (state.resolve planned.target)
      (Detail.applyPredicate state planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate state)))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionStepValid semanticContext
      (committed.applySubstitution state.inference.substitution) := by
  apply CoercionStepValid.intro
      (primary := Detail.applyPredicate state planned.predicate)
      (methodPredicates :=
        planned.methodPredicates.map (Detail.applyPredicate state))
  · simpa [CoercionStep.applySubstitution, State.resolve,
      TypeSystem.InferState.resolve, corresponds.source_eq,
      corresponds.target_eq] using profile
  · simpa [CoercionStep.applySubstitution] using
      solveRequirements_committedCoercionStepSequenceProves corresponds
        success solved_eq valid

private theorem committed_member_has_planned_correspondence
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

/-- Structural search validity, exact commit correspondence, normalized
profile validity for every planned edge, and a valid solved ledger compose to
the declarative validity of the complete committed coercion path. -/
theorem committedCoercionPlanValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (structural : Detail.PlannedCoercionPath.isValid source target plan = true)
    (profiles : ∀ planned, planned ∈ plan →
      CoercionProfileInstantiates semanticContext
        ((Detail.commitCoercionPlan state plan).2.resolve planned.source)
        ((Detail.commitCoercionPlan state plan).2.resolve planned.target)
        (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2
          planned.predicate)
        (planned.methodPredicates.map
          (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2)))
    (success : Detail.solveRequirements inferenceContext
      (Detail.commitCoercionPlan state plan).2
      (Detail.commitCoercionPlan state plan).2.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      ((Detail.commitCoercionPlan state plan).2.resolve source)
      ((Detail.commitCoercionPlan state plan).2.resolve target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          (Detail.commitCoercionPlan state plan).2.inference.substitution)) := by
  let committed := Detail.commitCoercionPlan state plan
  have committedStructural :
      Frontend.SourceInference.CoercionPath.isValid source target
        committed.1 = true :=
    Detail.commitCoercionPlan_isValid state plan structural
  have normalizedStructural :
      Frontend.SourceInference.CoercionPath.isValid
        (committed.2.resolve source) (committed.2.resolve target)
        (committed.1.map
          (CoercionStep.applySubstitution
            committed.2.inference.substitution)) = true := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
      Frontend.SourceInference.CoercionPath.isValid_applySubstitution
        committed.2.inference.substitution committedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp stepMember
  have correspondences := Detail.commitCoercionPlan_corresponds state plan
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence correspondences originalMember
  exact committedCoercionStepValid correspondence
    (profiles planned plannedMember) success solved_eq valid

/-- Every solved row classified as a qualified-local template by the input
state retains the canonical assumption evidence for its normalized
predicate. -/
theorem solveRequirements_template_evidence
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    ∀ row, row ∈ solved → row.id ∈ state.localSchemeAssumptions →
      row.evidence = .assumption row.predicate := by
  have corresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil =>
      intro row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro candidate member template
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have requirement_template :
            requirement.id ∈ state.localSchemeAssumptions := by
          rw [← id_eq]
          exact template
        have evidence_eq := solveRequirementEvidence_template_eq
          requirement_template evidence_success
        rw [predicate_eq]
        exact evidence_eq
      · exact induction candidate member template

/-- When no input row is a qualified-local template, successful ledger
solving validates every output row in a declarative context with the same
catalog and normalized declaration assumptions. -/
theorem solveRequirements_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (ordinary : ∀ requirement, requirement ∈ requirements →
      requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    SolvedRequirementsValid semanticContext solved := by
  have corresponds := solveRequirements_corresponds success
  clear success
  unfold SolvedRequirementsValid
  revert ordinary
  induction corresponds with
  | nil =>
      intro _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro ordinary candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have valid := solveRequirementEvidence_ordinary_sound
          (semanticContext := semanticContext)
          (ordinary requirement (by simp)) signatures_eq assumptions_eq
          evidence_success
        have candidate_eq : candidate = {
            id := requirement.id
            predicate := Detail.applyPredicate state requirement.predicate
            evidence := candidate.evidence
          } := by
          cases candidate
          simp_all
        rw [candidate_eq]
        exact valid
      · exact induction (fun tailRequirement tailMember =>
          ordinary tailRequirement (by simp [tailMember])) candidate member

/-- Successful ledger solving validates ordinary rows through retained trait
evidence and qualified-local template rows through their exact
initializer-scoped source ownership. -/
theorem solveRequirements_scoped_entries_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {source : TypedSource}
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (template_iff : ∀ requirement, requirement ∈ requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (template_scoped : ∀ requirement, requirement ∈ requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    ∀ row, row ∈ solved →
      ScopedRequirementEntryValid semanticContext source row := by
  have corresponds := solveRequirements_corresponds success
  clear success
  revert template_iff template_scoped
  induction corresponds with
  | nil =>
      intro _ _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro template_iff template_scoped candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        by_cases template : requirement.id ∈ state.localSchemeAssumptions
        · have evidence_eq := solveRequirementEvidence_template_eq template
            evidence_success
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := .assumption
                (Detail.applyPredicate state requirement.predicate)
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .template (template_scoped requirement (by simp) template)
        · have valid := solveRequirementEvidence_ordinary_sound
            (semanticContext := semanticContext) template signatures_eq
            assumptions_eq evidence_success
          have not_template : requirement.id ∉
              sourceLocalSchemeTemplateIds source := by
            intro source_member
            exact template ((template_iff requirement (by simp)).mpr
              source_member)
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := candidate.evidence
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .ordinary not_template valid
      · exact induction
          (fun tailRequirement tailMember =>
            template_iff tailRequirement (by simp [tailMember]))
          (fun tailRequirement tailMember template =>
            template_scoped tailRequirement (by simp [tailMember]) template)
          candidate member

/-- A canonical inference ledger with complete source-template coverage
becomes a whole-body scoped requirement ledger after successful solving. -/
theorem solveRequirements_scoped_ledger_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {baseContext : SourceSemantics.Context}
    {source : TypedSource}
    (stateWellFormed : state.RequirementsWellFormed)
    (signatures_eq : baseContext.signatures = inferenceContext.signatures)
    (assumptions_eq : baseContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (templateOwnership : LocalSchemeTemplateOwnership source)
    (template_iff : ∀ requirement, requirement ∈ state.requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (templates_subset : sourceLocalSchemeTemplateIds source ⊆
      state.requirements.map (fun requirement => requirement.id))
    (template_scoped : ∀ requirement, requirement ∈ state.requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved) :
    ScopedRequirementLedgerWellFormed
      (baseContext.withSolvedRequirements solved) source := by
  refine {
    idsUnique := ?_
    templateOwnership := templateOwnership
    entriesValid := ?_
    templatesComplete := ?_
  }
  · change (solved.map (fun requirement => requirement.id)).Nodup
    exact Detail.solveRequirements_ids_nodup inferenceContext state solved
      stateWellFormed success
  · exact solveRequirements_scoped_entries_sound
      (semanticContext := baseContext.withSolvedRequirements solved)
      signatures_eq assumptions_eq template_iff template_scoped success
  · intro owner contains
    have templateMember : owner.requirement.templateRequirement ∈
        sourceLocalSchemeTemplateIds source :=
      sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
    have inputMember : owner.requirement.templateRequirement ∈
        state.requirements.map (fun requirement => requirement.id) :=
      templates_subset templateMember
    have ids_eq := Detail.solveRequirements_preserves_ids inferenceContext state
      state.requirements solved success
    have outputMember : owner.requirement.templateRequirement ∈
        solved.map (fun requirement => requirement.id) := by
      rw [ids_eq]
      exact inputMember
    rcases List.mem_map.mp outputMember with ⟨row, member, id_eq⟩
    exact ⟨row, member, id_eq⟩

/-- Qualified-local template identities materialized directly by one source
node.  Expression nodes never materialize binders; statement nodes may retain
an initialized `let` directly or in a `for` header. -/
def nodeLocalSchemeTemplateIds : Node → List RequirementId
  | .expression _ => []
  | .statement statement =>
      (statementInitializedLetBindings statement.form).flatMap fun binding =>
        binding.binder.schemeRequirements.map
          (fun requirement => requirement.templateRequirement)

/-- Appending one node appends exactly that node's qualified-local template
identity inventory. -/
theorem recordNode_sourceLocalSchemeTemplateIds
    (state : Frontend.SourceInference.State) (node : Node)
    (roots : List NodeId) :
    sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource roots) =
      sourceLocalSchemeTemplateIds (state.toTypedSource roots) ++
        nodeLocalSchemeTemplateIds node := by
  cases node with
  | expression expression =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, nodeLocalSchemeTemplateIds]
  | statement statement =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, InitializedLetBinding.templateOwners,
        nodeLocalSchemeTemplateIds, List.map_flatMap,
        List.map_map, Function.comp_def]

/-- ID-only ghost invariant for source-inference template tracking.  The
`pending` suffix contains template identities allocated into binders whose
owning statement node has not yet been recorded. -/
structure TemplateTracking (state : Frontend.SourceInference.State)
    (pending : List RequirementId) : Prop where
  classified : state.localSchemeAssumptions.Perm
    (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
  unique : state.localSchemeAssumptions.Nodup
  covered : ∀ id, id ∈ state.localSchemeAssumptions →
    id ∈ state.requirements.map (fun requirement => requirement.id)

namespace TemplateTracking

/-- Initial inference states contain neither source-owned nor pending local
scheme templates. -/
theorem initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment := [])
    (comptime : List Bool := []) :
    TemplateTracking
      (Frontend.SourceInference.State.initial owner locals comptime) [] := by
  constructor <;>
    simp [Frontend.SourceInference.State.initial,
      Frontend.SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings]

/-- Replacing only the executable local type environment leaves template
classification, uniqueness, and requirement-ledger coverage unchanged.  This
is the exact state update performed immediately before let-binder allocation. -/
theorem replaceLocals
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (locals : TypeSystem.Environment) :
    TemplateTracking { state with locals := locals } pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Allocating a binder moves its qualified requirement identities into the
pending suffix.  Canonical generalization supplies the three side conditions:
new identities are distinct, fresh for the classification, and already occur
in the input requirement ledger. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    (newUnique :
      (schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)).Nodup)
    (newFresh : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∉ state.localSchemeAssumptions)
    (newCovered : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∈ state.requirements.map (fun requirement => requirement.id)) :
    TemplateTracking
      (state.allocateBinder name scheme span comptime schemeRequirements).2
      (pending ++ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)) := by
  let added := schemeRequirements.map (fun requirement =>
    requirement.templateRequirement)
  constructor
  · change (state.localSchemeAssumptions ++ added).Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
        (pending ++ added))
    simpa only [List.append_assoc] using tracked.classified.append_right added
  · change (state.localSchemeAssumptions ++ added).Nodup
    rw [List.nodup_append]
    refine ⟨tracked.unique, (by simpa [added] using newUnique), ?_⟩
    intro old oldMember new newMember same
    subst new
    exact newFresh old (by simpa [added] using newMember) oldMember
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    change id ∈ state.localSchemeAssumptions ++ added at member
    rcases List.mem_append.mp member with oldMember | addedMember
    · exact tracked.covered id oldMember
    · exact newCovered id (by simpa [added] using addedMember)

/-- Canonical local generalization discharges every side condition required
by template-tracking binder allocation.  The executable let paths first
replace `locals` with its substituted form and then perform exactly this
allocation. -/
theorem allocateGeneralizedValue
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (requirementsWellFormed : state.RequirementsWellFormed)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty) (name : String)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false) :
    let generalized := Frontend.SourceInference.Detail.generalizeValue state
      locals requirementStart type
    TemplateTracking
      (({ state with locals := locals }).allocateBinder name
        generalized.scheme span comptime generalized.requirements).2
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  dsimp only
  apply allocateBinder (tracked.replaceLocals locals) name
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).scheme span comptime
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).requirements
  · exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).nodup
        (Frontend.SourceInference.State.requirementIds_nodup state
          requirementsWellFormed)
  · intro id member
    change id ∉ state.localSchemeAssumptions
    exact Frontend.SourceInference.Detail.generalizeValue_templateIds_fresh
      state locals requirementStart type id member
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).subset member

/-- Recording a node materializes a pending suffix matching that node's exact
template inventory; older ambient pending identities remain pending. -/
theorem recordNode
    {state : Frontend.SourceInference.State}
    {ambient : List RequirementId} {node : Node}
    (tracked : TemplateTracking state
      (ambient ++ nodeLocalSchemeTemplateIds node)) :
    TemplateTracking (state.recordNode node) ambient := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource []) ++
        ambient)
    rw [recordNode_sourceLocalSchemeTemplateIds]
    have swapped :
        (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (ambient ++ nodeLocalSchemeTemplateIds node)).Perm
          (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (nodeLocalSchemeTemplateIds node ++ ambient)) :=
      List.Perm.append_left _ List.perm_append_comm
    simpa only [List.append_assoc] using tracked.classified.trans swapped
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Lexical restoration changes neither the emitted node table nor executable
template classification and therefore preserves every pending suffix. -/
theorem restoreLexicalScope
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (scope : Frontend.SourceInference.LexicalScope) :
    TemplateTracking (state.restoreLexicalScope scope) pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Once no template identity remains pending, the materialized source owns
globally unique qualified-template identities. -/
theorem ownership
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    LocalSchemeTemplateOwnership (state.toTypedSource roots) := by
  constructor
  have sourceUnique :
      (sourceLocalSchemeTemplateIds (state.toTypedSource [])).Nodup := by
    simpa using tracked.classified.nodup_iff.mp tracked.unique
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using sourceUnique

/-- With an empty pending suffix, executable classification and materialized
source ownership classify exactly the same stable identities. -/
theorem classified_iff
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := [])
    (id : RequirementId) :
    id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) := by
  have aligned : id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ [] :=
    tracked.classified.mem_iff
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using aligned

/-- Every fully materialized source template identity comes from an input
requirement row. -/
theorem source_ids_subset_requirements
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    sourceLocalSchemeTemplateIds (state.toTypedSource roots) ⊆
      state.requirements.map (fun requirement => requirement.id) := by
  intro id sourceMember
  exact tracked.covered id ((tracked.classified_iff roots id).mpr sourceMember)

end TemplateTracking

/-- The source-owned qualified-local template identities materialized from a
state agree exactly with the state's executable template classification. -/
def TemplateIdsAligned (state : Frontend.SourceInference.State)
    (roots : List NodeId) : Prop :=
  ∀ id, id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) ↔
    id ∈ state.localSchemeAssumptions

/-- Final substitution preserves source template identities, so an alignment
established before finalization remains visible in the emitted typed source. -/
theorem finalize_templateIdsAligned
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ id, id ∈ sourceLocalSchemeTemplateIds result.typedSource ↔
      id ∈ state.localSchemeAssumptions := by
  intro id
  rw [Detail.finalize_typedSource success]
  simp only [FlexibleSubstitution.sourceLocalSchemeTemplateIds_applySubstitution]
  exact aligned id

/-- A template row in a successfully finalized source retains canonical
assumption evidence whenever the input state's executable classification is
aligned with the source-owned template identities. -/
theorem finalize_template_evidence
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ row, row ∈ result.solvedRequirements →
      row.id ∈ sourceLocalSchemeTemplateIds result.typedSource →
      row.evidence = .assumption row.predicate := by
  intro row member template
  have initialTemplate : row.id ∈ state.localSchemeAssumptions :=
    (finalize_templateIdsAligned aligned success row.id).mp template
  unfold Detail.finalize at success
  cases patternResult :
      Detail.defaultIntegerPatternTargets state.integerPatterns state with
  | error error =>
      simp [patternResult, bind, Except.bind] at success
  | ok patternState =>
      cases literalResult :
          Detail.defaultIntegerLiteralTargets patternState.integerLiterals
            patternState with
      | error error =>
          simp [patternResult, literalResult, bind, Except.bind] at success
      | ok finalState =>
          have finalTemplate : row.id ∈
              finalState.localSchemeAssumptions := by
            rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
              literalResult,
              Detail.defaultIntegerPatternTargets_localSchemeAssumptions
                patternResult]
            exact initialTemplate
          cases validationResult :
              Detail.validateIntegerLiteralTargets finalState
                finalState.integerLiterals with
          | error error =>
              simp [patternResult, literalResult, validationResult, bind,
                Except.bind] at success
          | ok validation =>
              cases requirementsResult :
                  Detail.solveRequirements inferenceContext finalState
                    finalState.requirements with
              | error error =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
              | ok requirements =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
                  cases success
                  exact solveRequirements_template_evidence requirementsResult
                    row member finalTemplate

/-- Proof-facing context for the requirement ledger emitted by finalization.
Both declaration assumptions and solved predicates use the final inference
substitution, while the complete solved ledger is retained for later lookup. -/
def finalizedRequirementContext
    (inferenceContext : Frontend.SourceInference.Context)
    (result : Frontend.SourceInference.Result) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures inferenceContext.signatures)
    |>.withAssumptions
      (inferenceContext.assumptions.map
        (TypedTraitResolution.applySubstitution result.substitution)))
    |>.withSolvedRequirements result.solvedRequirements

/-- When finalization starts without qualified-local templates, every emitted
solved row has independently valid retained evidence in the finalized
requirement context. -/
theorem finalize_solvedRequirementsValid
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (ordinary : state.localSchemeAssumptions = [])
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    SolvedRequirementsValid
      (finalizedRequirementContext inferenceContext result)
      result.solvedRequirements := by
  unfold Detail.finalize at success
  cases patternResult :
      Detail.defaultIntegerPatternTargets state.integerPatterns state with
  | error error =>
      simp [patternResult, bind, Except.bind] at success
  | ok patternState =>
      have patternOrdinary : patternState.localSchemeAssumptions = [] := by
        rw [Detail.defaultIntegerPatternTargets_localSchemeAssumptions
          patternResult, ordinary]
      cases literalResult :
          Detail.defaultIntegerLiteralTargets patternState.integerLiterals
            patternState with
      | error error =>
          simp [patternResult, literalResult, bind, Except.bind] at success
      | ok finalState =>
          have finalOrdinary : finalState.localSchemeAssumptions = [] := by
            rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
              literalResult, patternOrdinary]
          cases validationResult :
              Detail.validateIntegerLiteralTargets finalState
                finalState.integerLiterals with
          | error error =>
              simp [patternResult, literalResult, validationResult, bind,
                Except.bind] at success
          | ok validation =>
              cases requirementsResult :
                  Detail.solveRequirements inferenceContext finalState
                    finalState.requirements with
              | error error =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
              | ok requirements =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
                  cases success
                  apply solveRequirements_ordinary_sound
                    (inferenceContext := inferenceContext)
                    (state := finalState)
                    (requirements := finalState.requirements)
                  · intro requirement member
                    rw [finalOrdinary]
                    simp
                  · rfl
                  · rfl
                  · exact requirementsResult

end Solcore.SourceSemantics.SourceInferenceSoundness

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend SourceInference TypeSystem

/-- Once the inference pass has supplied a semantically valid closing
substitution, successful finalization transports the corresponding declarative
body derivation to the emitted typed source and result type. -/
theorem finalize_bodyHasType
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId} {result : Result}
    {sourceContext targetContext : SourceSemantics.Context}
    {closedVariables : List TypeVarId} {facts : BodyFacts}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : ContextSubstitutionValid result.substitution
      closedVariables sourceContext targetContext)
    (typing : BodyHasType (state.toTypedSource roots) sourceContext type facts) :
    BodyHasType result.typedSource targetContext result.type
      (applyBodyFacts result.substitution facts) := by
  rw [Detail.finalize_typedSource success, Detail.finalize_type success]
  exact BodyHasType.applySubstitution catalog contextValid typing

end Solcore.SourceSemantics.FlexibleSubstitution
