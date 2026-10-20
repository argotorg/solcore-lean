import Solcore.SourceSemantics.UnificationFormation
import Solcore.Frontend.SourceInference.Resolution

/-! Intermediate coercion types formed by real catalog freshening and matching. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend TypeSystem

private theorem occurs_applyMany (parameter : TypeParameterId) (head : Ty) (arguments : List Ty) :
    TypeParameterOccurs parameter (Ty.applyMany head arguments) ↔
      TypeParameterOccurs parameter head ∨ ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change TypeParameterOccurs parameter (Ty.applyMany (.application head argument) rest) ↔ _
    rw [ih]
    simp only [TypeSystem.TypeParameterOccurs, List.mem_cons, exists_eq_or_imp, or_assoc]

private theorem occurs_nominal {parameter : TypeParameterId} {declaration : Resolved.DeclarationId} {arguments : List Ty}
    (occurs : TypeParameterOccurs parameter (Ty.nominal declaration arguments)) :
    ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  rcases (occurs_applyMany parameter (.constructor (.declaration declaration)) arguments).mp occurs with impossible | found
  · cases impossible
  · exact found


private theorem parameter_occurs_mem {context : Context} {variables : List TypeVarId}
    {type : Ty} (formed : TypeWellScoped context variables type) :
    ∀ parameter, TypeParameterOccurs parameter type → parameter ∈ context.typeParameters := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => ∀ parameter, TypeParameterOccurs parameter type →
      parameter ∈ context.typeParameters)
    (motive_2 := fun types _ => ∀ type ∈ types, ∀ parameter,
      TypeParameterOccurs parameter type → parameter ∈ context.typeParameters)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ formed
  · intro metavariable _ parameter occurs; cases occurs
  · intro actual bound _ parameter occurs; cases occurs; exact bound
  · intro builtin parameter occurs; cases occurs
  · intro declaration arguments _ _ _ ih parameter occurs
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    exact ih argument member parameter occurs
  · intro declaration arguments _ _ _ ih parameter occurs
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    exact ih argument member parameter occurs
  · intro left right _ _ leftIH rightIH parameter occurs
    exact occurs.elim (leftIH parameter) (rightIH parameter)
  · intro left right _ _ leftIH rightIH parameter occurs
    exact occurs.elim (leftIH parameter) (rightIH parameter)
  · intro left right _ _ leftIH rightIH parameter occurs
    exact occurs.elim (leftIH parameter) (rightIH parameter)
  · intro inner _ ih parameter occurs; exact ih parameter occurs
  · intro inner _ ih parameter occurs; exact ih parameter occurs
  · intro type member; cases member
  · intro head tail _ _ headIH tailIH type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH type member

private theorem predicate_parameter_mem {context : Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) {parameter : TypeParameterId}
    (occurs : TypedTraitResolution.ParameterOccursInPredicate parameter predicate) :
    parameter ∈ context.typeParameters := by
  rcases occurs with occurs | ⟨argument, member, occurs⟩
  · exact parameter_occurs_mem formed.subject.typeWellScoped parameter occurs
  · exact parameter_occurs_mem (formed.arguments argument member).typeWellScoped parameter occurs

private theorem predicate_no_variable {context : Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) (metavariable : TypeVarId) :
    ¬ TypedTraitResolution.VariableOccursInPredicate metavariable predicate := by
  rintro (occurs | ⟨argument, member, occurs⟩)
  · simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed.subject] at occurs
  · simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
      (formed.arguments argument member)] at occurs

/-- The actual rule collector has precisely the parameters of its real
implementation signature. The real freshening allocator therefore replaces
every rigid parameter by an admissible residual variable. -/
theorem coercion_rule_fresh_head_types
    {context : Context} {rule : ProgramImplRule}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (member : rule ∈ context.signatures.implRules) (goal : ProgramPredicate) :
    TypeAdmissible context (TypedTraitResolution.freshenRuleFor rule goal).head.subject ∧
    (∀ argument ∈ (TypedTraitResolution.freshenRuleFor rule goal).head.arguments,
      TypeAdmissible context argument) := by
  rw [catalog.impl_rules_eq] at member
  obtain ⟨signature, signatureMember, rfl⟩ := List.mem_map.mp member
  have formed := catalog.implementations_semantic signature signatureMember
  have closed : TypedTraitResolution.ruleVariables signature.implRule = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro metavariable member
    rcases TypedTraitResolution.mem_ruleVariables_occurs_iff.mp member with
      occurs | ⟨predicate, predicateMember, occurs⟩
    · exact predicate_no_variable formed.head metavariable occurs
    · exact predicate_no_variable (formed.predicates predicate predicateMember) metavariable occurs
  obtain ⟨substitution, domain, variables, headEq⟩ :=
    TypedTraitResolution.freshenRuleFor_head_of_no_variables signature.implRule goal closed
  have domainPerm : (TypedTraitResolution.ruleParameters signature.implRule).Perm
      signature.parameters := by
    apply (List.perm_ext_iff_of_nodup
      (TypedTraitResolution.ruleParameters_nodup _) formed.parameters_nodup).mpr
    intro parameter
    constructor
    · intro member
      rcases TypedTraitResolution.mem_ruleParameters_occurs_iff.mp member with
        occurs | ⟨predicate, predicateMember, occurs⟩
      · exact predicate_parameter_mem formed.head occurs
      · exact predicate_parameter_mem (formed.predicates predicate predicateMember) occurs
    · intro member
      exact TypedTraitResolution.mem_ruleParameters_occurs_iff.mpr
        (.inl (formed.parameters_in_head parameter member))
  have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact substitution
      signature.parameters := ⟨formed.parameters_nodup, by
        simpa only [SourceSemantics.ParameterSubstitution.domain, domain] using domainPerm⟩
  have range : SourceSemantics.ParameterSubstitution.RangeAdmissible context substitution := by
    intro parameter replacement member
    obtain ⟨fresh, rfl⟩ := variables parameter replacement member
    exact TypeAdmissible.variableOfResidual binders residual fresh
  rw [headEq]
  constructor
  · exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      (source := signatureContext context.signatures signature.id signature.parameters signature.wherePredicates)
      substitution exactSubstitution range rfl binders formed.head.subject.typeWellScoped
  · intro argument member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
      (source := signatureContext context.signatures signature.id signature.parameters signature.wherePredicates)
      substitution exactSubstitution range rfl binders
      (formed.head.arguments original originalMember).typeWellScoped

/-- Matching a fresh head without changing the caller's type yields formed
substitutions; applying that actual substitution forms the generated target. -/
theorem coercion_rule_edge_target
    {context : Context} {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : SourceInference.Detail.CoercionEdge}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (residual : context.residualTypeVariables = true)
    (member : rule ∈ context.signatures.implRules)
    (sourceFormed : TypeAdmissible context source)
    (accepted : SourceInference.Detail.coercionRuleEdge? trait source rule = some edge) :
    edge.source = source ∧ TypeAdmissible context edge.target ∧
      edge.predicate = { trait, subject := source, arguments := [edge.target] } := by
  let goal : ProgramPredicate := { trait := .declaration trait, subject := source, arguments := [source] }
  have fresh := coercion_rule_fresh_head_types catalog sourceFormed.binders residual member goal
  dsimp only [goal] at fresh
  by_cases mismatch : (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [SourceInference.Detail.coercionRuleEdge?, mismatch] at accepted
  · simp only [SourceInference.Detail.coercionRuleEdge?, mismatch] at accepted
    cases arguments : (TypedTraitResolution.freshenRuleFor rule { trait := .declaration trait, subject := source, arguments := [source] }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at accepted
    | cons target rest =>
      cases rest with
      | cons second tail => simp [arguments, bind, Option.bind] at accepted
      | nil =>
        simp only [arguments, bind, Option.bind] at accepted
        cases unified : Unification.unify [{
            left := (TypedTraitResolution.freshenRuleFor rule { trait := .declaration trait, subject := source, arguments := [source] }).head.subject, right := source }] with
        | error error => simp [unified, Except.toOption] at accepted
        | ok substitution =>
          simp only [unified, Except.toOption] at accepted
          by_cases blocked : substitution.domain.any source.freeVariables.contains = true
          · simp [blocked] at accepted
          · by_cases ground : SourceInference.Detail.isGroundCoercionTarget (substitution.apply target) = true
            · simp [blocked, ground] at accepted
              subst edge
              refine ⟨rfl, ?_, rfl⟩
              have disjoint : ∀ metavariable, metavariable ∈ substitution.domain →
                  metavariable ∉ source.freeVariables := by
                intro metavariable domain occurs
                exact blocked (List.any_eq_true.mpr ⟨metavariable, domain, List.contains_iff_mem.mpr occurs⟩)
              have range := UnificationFormation.matching_range_admissible fresh.1 sourceFormed unified disjoint
              have solved := Unification.unifyTypes_solvedBelow
                ((Ty.variablesBelow_nextVariable _).weaken (Nat.le_max_left _ _))
                ((Ty.variablesBelow_nextVariable source).weaken (Nat.le_max_right _ _)) unified
              have targetFormed : TypeAdmissible context target := fresh.2 target (by rw [arguments]; simp)
              exact FlexibleSubstitution.TypeWellScoped.applyExactAdmissible sourceFormed.binders
                ⟨solved.domain_nodup, .refl _⟩ range
                (StructuralSubstitution.TypeWellScoped.weakenFlexible
                  (fun _ member => List.mem_append_left _ member) targetFormed.typeWellScoped)
            · simp [blocked, ground] at accepted

private theorem closed_predicate_apply {context : Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) (substitution : Substitution) :
    TypedTraitResolution.applySubstitution substitution predicate = predicate := by
  have unchanged (type : Ty) (typed : TypeWellFormed context type) :
      substitution.apply type = type :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type
      (by intro metavariable _ occurs; simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typed] at occurs)
  have subject := unchanged predicate.subject formed.subject
  have arguments : predicate.arguments.map substitution.apply = predicate.arguments := by
    calc
      predicate.arguments.map substitution.apply = predicate.arguments.map id :=
        List.map_congr_left (fun type member => unchanged type (formed.arguments type member))
      _ = predicate.arguments := List.map_id _

  cases predicate
  simp only [TypedTraitResolution.applySubstitution] at subject arguments ⊢
  rw [subject, arguments]

/-- An assumption edge uses an actual declared predicate. Closed declaration
formation makes its normalization inert, so its real target is already formed. -/
theorem coercion_assumption_edge_target
    {context : Context} {inferenceContext : SourceInference.Context}
    {state : SourceInference.State} {trait : Resolved.DeclarationId} {source : Ty}
    {edge : SourceInference.Detail.CoercionEdge}
    (assumptions : ∀ predicate ∈ inferenceContext.assumptions,
      PredicateWellFormed context predicate)
    (member : edge ∈ SourceInference.Detail.assumptionCoercionEdges inferenceContext state trait source) :
    edge.source = source ∧ TypeAdmissible context edge.target ∧
      PredicateAdmissible context edge.predicate := by
  unfold SourceInference.Detail.assumptionCoercionEdges at member
  obtain ⟨assumption, assumptionMember, produced⟩ := List.mem_filterMap.mp member
  have formed := assumptions assumption assumptionMember
  have unchanged : SourceInference.Detail.applyPredicate state assumption = assumption :=
    closed_predicate_apply formed state.inference.substitution
  dsimp only at produced
  rw [unchanged] at produced
  split at produced
  · cases produced
  · split at produced
    · rename_i target arguments
      split at produced
      · cases Option.some.inj produced
        exact ⟨rfl, TypeAdmissible.ofWellFormed
          (formed.arguments target (by rw [arguments]; simp)), ⟨TypeAdmissible.ofWellFormed formed.subject,
            fun argument member => TypeAdmissible.ofWellFormed (formed.arguments argument member), formed.trait⟩⟩
      · cases produced
    · cases produced

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
