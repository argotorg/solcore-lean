import Solcore.SourceSemantics.Internal.Formation.Requirements
import Solcore.SourceSemantics.Internal.Formation.CoercionTargets
import Solcore.SourceSemantics.Internal.Inference.LetCertificates
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Normalized coercions and operators

Final formation of coercion rows, retained requirements, operator obligations and the fitting of
arguments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedProducerFormation
/-! Actual producer predicates can be formed in the final inference context,
using the final types of their operands directly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

theorem predicate_applyParameters_normalized_admissible
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (outer : Substitution) (inner : TypeSystem.ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact inner source.typeParameters)
    (range : ∀ parameter replacement, (parameter, replacement) ∈ inner →
      TypeAdmissible target (outer.apply replacement))
    (signatures : target.signatures = source.signatures)
    (binders : TypeParameterBindersWellFormed target)
    (formed : PredicateWellFormed source predicate) :
    PredicateAdmissible target
      (TypedTraitResolution.applySubstitution outer (predicate.applyParameters inner)) := by
  rw [FlexibleSubstitution.PredicateWellFormed.applyFlexible_composeParameters outer inner exact formed]
  apply predicate_applyParameters_admissible
    (FlexibleSubstitution.ParameterSubstitution.mapRange outer inner)
    (FlexibleSubstitution.ParameterSubstitution.Exact.mapRange outer exact) ?_ signatures binders formed
  intro parameter replacement member
  obtain ⟨⟨original, type⟩, originalMember, same⟩ := List.mem_map.mp member
  cases same
  exact range original type originalMember

theorem operator_profile_predicates_normalized
    {context : SourceSemantics.Context} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandFormed : TypeAdmissible context (outer.apply operand))
    (profile : OperatorProfileInstantiates context traitName methodName operand parameters returns predicates) :
    ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  cases profile with
  | @intro signature method parameter signatureMember _ parametersEq methodUnique _ _ =>
    have signatureFormed := catalog.traits_semantic signature signatureMember
    have methodMember : method ∈ signature.methods := by
      have filtered : method ∈ signature.methods.filter
          (fun candidate => candidate.name == methodName) := by
        rw [methodUnique]
        simp
      exact (List.mem_filter.mp filtered).1
    have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
        [(parameter, operand)] signature.parameters := by
      rw [parametersEq]
      exact SourceSemantics.ParameterSubstitution.exact_singleton _ _
    intro predicate member
    rcases List.mem_cons.mp member with rfl | member
    · change PredicateAdmissible context
        {trait := .declaration signature.id, subject := outer.apply operand, arguments := []}
      exact ⟨operandFormed, by simp,
        signature, signatureMember, rfl, by simp [parametersEq]⟩
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      apply predicate_applyParameters_normalized_admissible
        (source := signatureContext context.signatures signature.id signature.parameters
          (signature.wherePredicates ++ method.wherePredicates))
        (target := context)
        outer [(parameter, operand)] exactSubstitution ?_ rfl operandFormed.binders
        ((signatureFormed.methods method methodMember).predicates original originalMember)
      intro candidate replacement member
      cases List.mem_singleton.mp member
      exact operandFormed

theorem operator_issuance_normalized
    {inferenceContext : SourceInference.Context} {context : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (signatures : context.signatures = inferenceContext.signatures)
    (traitNameEq : (inferenceContext.signatures.trait? trait).map (·.name) = some traitName)
    (operandFormed : TypeAdmissible context (outer.apply operand))
    (accepted : Detail.operatorTraitPredicates inferenceContext trait methodName operand
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) :=
  operator_profile_predicates_normalized catalog operandFormed
    (operatorTraitPredicates_instantiates signatures traitNameEq accepted)

theorem coercion_issuance_normalized
    {inferenceContext : SourceInference.Context} {context : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate} {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (signatures : context.signatures = inferenceContext.signatures)
    (sourceFormed : TypeAdmissible context (outer.apply source))
    (targetFormed : TypeAdmissible context (outer.apply target))
    (profileAccepted : Detail.coercionMethodProfile? inferenceContext trait = .ok profile)
    (predicatesAccepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer
      {trait := .declaration trait, subject := source, arguments := [target]}) ∧
      ∀ predicate ∈ predicates,
        PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  obtain ⟨signature, signatureMember, idEq, arity, selectedOrigin⟩ :=
    coercion_profile_origin profileAccepted
  have semanticMember : signature ∈ context.signatures.traits := signatures.symm ▸ signatureMember
  have signatureFormed := catalog.traits_semantic signature semanticMember
  constructor
  · exact ⟨sourceFormed, by intro argument member; cases List.mem_singleton.mp member; exact targetFormed,
      signature, semanticMember, idEq, arity.symm⟩
  · cases profile with
    | none =>
      simp [Detail.coercionMethodPredicates] at predicatesAccepted
      subst predicates
      simp
    | some profile =>
      have origin := selectedOrigin profile (by simp)
      have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
          (profile.parameters.zip [source, target]) signature.parameters := by
        rw [origin.2.1]
        exact SourceSemantics.ParameterSubstitution.exact_zip
          signatureFormed.parameters_nodup (by simpa using arity.symm)
      simp only [Detail.coercionMethodPredicates] at predicatesAccepted
      split at predicatesAccepted
      · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at predicatesAccepted
        cases predicatesAccepted
        intro predicate member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply predicate_applyParameters_normalized_admissible
          (source := signatureContext context.signatures signature.id signature.parameters
            (signature.wherePredicates ++ profile.method.wherePredicates))
          (target := context)
          outer (profile.parameters.zip [source, target]) exactSubstitution ?_
          rfl sourceFormed.binders
          ((signatureFormed.methods profile.method origin.2.2).predicates original originalMember)
        intro parameter replacement member
        have choice := (List.of_mem_zip member).2
        rcases List.mem_cons.mp choice with rfl | choice
        · exact sourceFormed
        · cases List.mem_singleton.mp choice
          exact targetFormed
      · simp [throw, Functor.map, Except.map] at predicatesAccepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCoercionTargets
/-! Actual coercion matching produces formed intermediate targets directly
under the selected finalizer's substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem

theorem coercion_rule_edge_target_normalized
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : Detail.CoercionEdge} {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (residual : context.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible context outer)
    (member : rule ∈ context.signatures.implRules)
    (sourceFormed : TypeAdmissible context (outer.apply source))
    (accepted : Detail.coercionRuleEdge? trait source rule = some edge) :
    edge.source = source ∧ TypeAdmissible context (outer.apply edge.target) ∧
      edge.predicate = {trait, subject := source, arguments := [edge.target]} := by
  let goal : ProgramPredicate := {trait := .declaration trait, subject := source, arguments := [source]}
  have fresh := coercion_rule_fresh_head_types catalog sourceFormed.binders residual member goal
  dsimp only [goal] at fresh
  by_cases mismatch : (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [Detail.coercionRuleEdge?, mismatch] at accepted
  · simp only [Detail.coercionRuleEdge?, mismatch] at accepted
    cases arguments : (TypedTraitResolution.freshenRuleFor rule
        {trait := .declaration trait, subject := source, arguments := [source]}).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at accepted
    | cons target rest =>
      cases rest with
      | cons second tail => simp [arguments, bind, Option.bind] at accepted
      | nil =>
        simp only [arguments, bind, Option.bind] at accepted
        cases unified : Unification.unify [{
            left := (TypedTraitResolution.freshenRuleFor rule
              {trait := .declaration trait, subject := source, arguments := [source]}).head.subject,
            right := source}] with
        | error error => simp [unified, Except.toOption] at accepted
        | ok substitution =>
          simp only [unified, Except.toOption] at accepted
          by_cases blocked : substitution.domain.any source.freeVariables.contains = true
          · simp [blocked] at accepted
          · by_cases ground : Detail.isGroundCoercionTarget (substitution.apply target) = true
            · simp [blocked, ground] at accepted
              subst edge
              refine ⟨rfl, ?_, rfl⟩
              have disjoint : ∀ metavariable, metavariable ∈ substitution.domain →
                  metavariable ∉ source.freeVariables := by
                intro metavariable domain occurs
                exact blocked (List.any_eq_true.mpr
                  ⟨metavariable, domain, List.contains_iff_mem.mpr occurs⟩)
              have matched := UnificationFormation.matching_normalized_range_admissible
                fresh.1 sourceFormed unified disjoint
              have composedRange : SubstitutionRangeAdmissible context (outer.compose substitution) := by
                intro metavariable replacement member
                rcases List.mem_append.mp member with updated | outerMember
                · obtain ⟨⟨original, type⟩, originalMember, same⟩ := List.mem_map.mp updated
                  cases same
                  exact matched original type originalMember
                · exact outerRange metavariable replacement (List.mem_filter.mp outerMember).1
              have targetFormed := fresh.2 target (by rw [arguments]; simp)
              simpa only [Substitution.compose_apply] using
                type_applySubstitution_residual residual composedRange targetFormed
            · simp [blocked, ground] at accepted

theorem coercion_assumption_edge_target_normalized
    {context : SourceSemantics.Context} {inferenceContext : SourceInference.Context} {state : State}
    {trait : Resolved.DeclarationId}
    {source : Ty} {edge : Detail.CoercionEdge} {outer : Substitution}
    (residual : context.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible context outer)
    (formed : ∀ predicate ∈ inferenceContext.assumptions, PredicateWellFormed context predicate)
    (member : edge ∈ Detail.assumptionCoercionEdges inferenceContext state trait source) :
    edge.source = source ∧ TypeAdmissible context (outer.apply edge.target) ∧
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer edge.predicate) := by
  have result := coercion_assumption_edge_target formed member
  exact ⟨result.1, type_applySubstitution_residual residual outerRange result.2.1,
    predicate_applySubstitution_residual residual outerRange result.2.2⟩

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCoercionGraph
/-! Final normalized formation follows every branch of actual coercion search. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

structure FormationContext (semantic : SourceSemantics.Context)
    (context : SourceInference.Context) (outer : Substitution) : Prop
    extends CoercionFormationContext semantic context where
  range : SubstitutionRangeAdmissible semantic outer

private def EdgeFormed (semantic : SourceSemantics.Context) (outer : Substitution) (edge : Detail.CoercionEdge) : Prop :=
  TypeAdmissible semantic (outer.apply edge.source) ∧ TypeAdmissible semantic (outer.apply edge.target) ∧
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer edge.predicate)

private def FullEdgeFormed (semantic : SourceSemantics.Context) (outer : Substitution) (edge : Detail.CoercionEdge) : Prop :=
  EdgeFormed semantic outer edge ∧ ∀ predicate ∈ edge.methodPredicates, PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate)

private theorem primary_formed {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile} {source target : Ty}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (sourceFormed : TypeAdmissible semantic (outer.apply source)) (targetFormed : TypeAdmissible semantic (outer.apply target)) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer {trait, subject := source, arguments := [target]}) := by
  obtain ⟨signature, member, idEq, arity, _⟩ := coercion_profile_origin profileAccepted
  exact ⟨sourceFormed, by intro argument member; cases List.mem_singleton.mp member; exact targetFormed,
    signature, formation.signatures.symm ▸ member, idEq, arity.symm⟩

private theorem attachMethods_formed {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {trait : Resolved.DeclarationId} {profile : Option Detail.CoercionMethodProfile}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (edges : List Detail.CoercionEdge) (rawFormed : ∀ edge ∈ edges, EdgeFormed semantic outer edge)
    {results : List Detail.CoercionEdge}
    (accepted : edges.mapM (fun edge => do
      let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
      pure { edge with methodPredicates }) = Except.ok results) :
    ∀ edge ∈ results, FullEdgeFormed semantic outer edge := by
  induction edges generalizing results with
  | nil => simp at accepted; subst results; simp
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases methods : Detail.coercionMethodPredicates profile head.source head.target with
    | error error => simp [methods, bind, Except.bind] at accepted
    | ok predicates =>
      simp only [methods, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      cases tails : tail.mapM (fun edge => do
          let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
          pure { edge with methodPredicates }) with
      | error error =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp [tails] at accepted
      | ok rest =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp only [tails, Except.ok.injEq] at accepted
        subst results
        intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · have raw := rawFormed head (by simp)
          exact ⟨raw, (coercion_issuance_normalized formation.catalog formation.signatures
            raw.1 raw.2.1 profileAccepted methods).2⟩
        · exact ih (fun edge member => rawFormed edge (by simp [member])) tails edge member

private theorem coercionEdges_formed {semantic : SourceSemantics.Context} {outer : Substitution} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty} {edges : List Detail.CoercionEdge}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (sourceFormed : TypeAdmissible semantic (outer.apply source))
    (accepted : Detail.coercionEdges context state profile trait source = .ok edges) :
    ∀ edge ∈ edges, FullEdgeFormed semantic outer edge := by
  apply attachMethods_formed formation profileAccepted _ _ accepted
  intro edge member
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with rules | assumptions
  · obtain ⟨rule, ruleMember, produced⟩ := List.mem_filterMap.mp rules
    have result := coercion_rule_edge_target_normalized formation.catalog formation.residual formation.range
      (formation.signatures.symm ▸ ruleMember) sourceFormed produced
    refine ⟨result.1.symm ▸ sourceFormed, result.2.1, ?_⟩
    rw [result.2.2]
    exact primary_formed formation profileAccepted sourceFormed result.2.1
  · have result := coercion_assumption_edge_target_normalized formation.residual formation.range formation.assumptions assumptions
    exact ⟨result.1.symm ▸ sourceFormed, result.2⟩

def PlannedCoercionStepFormed (semantic : SourceSemantics.Context) (outer : Substitution)
    (step : Detail.PlannedCoercionStep) : Prop :=
  TypeAdmissible semantic (outer.apply step.source) ∧ TypeAdmissible semantic (outer.apply step.target) ∧
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer step.predicate) ∧
    ∀ predicate ∈ step.methodPredicates, PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate)

private def PathFormed (semantic : SourceSemantics.Context) (outer : Substitution)
    (path : Detail.CoercionPath) : Prop :=
  TypeAdmissible semantic (outer.apply path.current) ∧ ∀ step ∈ path.steps, PlannedCoercionStepFormed semantic outer step

private theorem viable_member {context : SourceInference.Context} {state : State}
    (edges : List Detail.CoercionEdge) {edge : Detail.CoercionEdge}
    (member : edge ∈ (Detail.viableCoercionEdges context state edges).viable) : edge ∈ edges := by
  induction edges with
  | nil => cases member
  | cons head tail ih =>
    unfold Detail.viableCoercionEdges at member
    cases viable : Detail.coercionEvidenceViable context state head.predicate head.methodPredicates with
    | error error =>
      simp only [viable] at member
      exact List.mem_cons_of_mem _ (ih member)
    | ok value =>
      cases value with
      | false =>
        simp only [viable] at member
        exact List.mem_cons_of_mem _ (ih member)
      | true =>
        simp only [viable, List.mem_cons] at member
        rcases member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih member)

private theorem expandPath_formed {semantic : SourceSemantics.Context} {outer : Substitution} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {path : Detail.CoercionPath}
    {result : Detail.CoercionExpansion}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (pathFormed : PathFormed semantic outer path)
    (accepted : Detail.expandCoercionPath context state profile trait path = .ok result) :
    ∀ next ∈ result.paths, PathFormed semantic outer next := by
  unfold Detail.expandCoercionPath at accepted
  cases edges : Detail.coercionEdges context state profile trait path.current with
  | error error => simp [edges, bind, Except.bind] at accepted
  | ok candidates =>
    simp only [edges, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro next member
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
    have safe := coercionEdges_formed formation profileAccepted pathFormed.1 edges edge
      (List.mem_filter.mp (viable_member _ edgeMember)).1
    refine ⟨safe.1.2.1, ?_⟩
    intro step stepMember
    rcases List.mem_append.mp stepMember with old | fresh
    · exact pathFormed.2 step old
    · cases List.mem_singleton.mp fresh
      exact ⟨safe.1.1, safe.1.2.1, safe.1.2.2, safe.2⟩

private theorem expandPaths_formed {semantic : SourceSemantics.Context} {outer : Substitution} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} (paths : List Detail.CoercionPath)
    {result : Detail.CoercionExpansion}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (pathsFormed : ∀ path ∈ paths, PathFormed semantic outer path)
    (accepted : Detail.expandCoercionPaths context state profile trait paths = .ok result) :
    ∀ next ∈ result.paths, PathFormed semantic outer next := by
  induction paths generalizing result with
  | nil => simp [Detail.expandCoercionPaths] at accepted; subst result; simp
  | cons head tail ih =>
    simp only [Detail.expandCoercionPaths] at accepted
    cases headResult : Detail.expandCoercionPath context state profile trait head with
    | error error => simp [headResult, bind, Except.bind] at accepted
    | ok first =>
      simp only [headResult, bind, Except.bind] at accepted
      cases tailResult : Detail.expandCoercionPaths context state profile trait tail with
      | error error => simp [tailResult] at accepted
      | ok rest =>
        simp only [tailResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro next member
        rcases List.mem_append.mp member with firstMember | restMember
        · exact expandPath_formed formation profileAccepted (pathsFormed _ (by simp)) headResult _ firstMember
        · exact ih (fun path member => pathsFormed path (by simp [member])) tailResult _ restMember

private theorem selectPath_formed {semantic : SourceSemantics.Context} {outer : Substitution}
    {source target : Ty} {paths : List Detail.CoercionPath}
    {steps : List Detail.PlannedCoercionStep}
    (pathsFormed : ∀ path ∈ paths, PathFormed semantic outer path)
    (accepted : Detail.selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic outer step := by
  unfold Detail.selectCoercionPath at accepted
  cases found : (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [found] at accepted
  | cons path rest =>
    cases rest with
    | cons second tail => simp [found] at accepted
    | nil =>
      simp only [found, Except.ok.injEq, Option.some.injEq] at accepted
      subst steps
      have member : path ∈ paths :=
        (List.mem_filter.mp (List.mem_eraseDups.mp
          (show path ∈ (paths.filter fun path => path.current == target).eraseDups by rw [found]; simp))).1
      exact (pathsFormed path member).2

private theorem finish_not_some {blocked : List Error} {steps : List Detail.PlannedCoercionStep}
    (accepted : Detail.finishCoercionSearch blocked = .ok (some steps)) : False := by
  cases blocked <;> simp [Detail.finishCoercionSearch] at accepted

private theorem searchPaths_formed {semantic : SourceSemantics.Context} {outer : Substitution} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    (fuel : Nat) {frontier : List Detail.CoercionPath} {blocked : List Error}
    {steps : List Detail.PlannedCoercionStep}
    (formation : FormationContext semantic context outer)
    (profileAccepted : Detail.coercionMethodProfile? context trait = .ok profile)
    (frontierFormed : ∀ path ∈ frontier, PathFormed semantic outer path)
    (accepted : Detail.searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic outer step := by
  induction fuel generalizing frontier blocked with
  | zero =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok beyond =>
      simp only [expanded, bind, Except.bind] at accepted
      split at accepted
      · exact (finish_not_some accepted).elim
      · cases accepted
  | succ fuel ih =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok next =>
      simp only [expanded, bind, Except.bind] at accepted
      have nextFormed := expandPaths_formed frontier formation profileAccepted frontierFormed expanded
      cases selected : Detail.selectCoercionPath source target next.paths with
      | error error => simp [selected] at accepted
      | ok option =>
        cases option with
        | some chosen =>
          simp only [selected, pure, Pure.pure, Except.pure,
            Except.ok.injEq, Option.some.injEq] at accepted
          subst steps
          exact selectPath_formed nextFormed selected
        | none =>
          simp only [selected] at accepted
          split at accepted
          · exact (finish_not_some accepted).elim
          · exact ih nextFormed accepted


/-- Every actual direct, searched or fallback step has formed endpoint types
and obligations. Intermediate targets come from catalog rules and declared
assumptions; the successful search does not supply its own formation premise. -/
theorem coercion_plan_formation {semantic : SourceSemantics.Context} {outer : Substitution} {state : State}
    {context : SourceInference.Context} {source target : Ty}
    {steps : List Detail.PlannedCoercionStep}
    (formation : FormationContext semantic context outer)
    (sourceFormed : TypeAdmissible semantic (outer.apply source))
    (targetFormed : TypeAdmissible semantic (outer.apply target))
    (accepted : Detail.coercionPlan? context state source target = .ok (some steps)) :
    ∀ step ∈ steps, PlannedCoercionStepFormed semantic outer step := by
  unfold Detail.coercionPlan? at accepted
  cases traitResult : Detail.conventionalTraitWithArity? context "Coerce" 2 with
  | error error => simp [traitResult, bind, Except.bind] at accepted
  | ok option =>
    cases option with
    | none => simp [traitResult, bind, Except.bind] at accepted
    | some trait =>
      simp only [traitResult, bind, Except.bind] at accepted
      cases profileResult : Detail.coercionMethodProfile? context trait with
      | error error => simp [profileResult] at accepted
      | ok profile =>
        simp only [profileResult] at accepted
        cases methodResult : Detail.coercionMethodPredicates profile source target with
        | error error => simp [methodResult] at accepted
        | ok methods =>
          simp only [methodResult] at accepted
          have methodsFormed := coercion_issuance_normalized formation.catalog
            formation.signatures sourceFormed targetFormed profileResult methodResult
          let direct : ProgramPredicate := {trait, subject := source, arguments := [target]}
          let directStep : Detail.PlannedCoercionStep := {
            source, target, predicate := direct, methodPredicates := methods
          }
          have directFormed : PlannedCoercionStepFormed semantic outer directStep :=
            ⟨sourceFormed, targetFormed, methodsFormed.1, methodsFormed.2⟩
          change (match Detail.coercionEvidenceViable context state direct methods with
            | .ok true => Except.ok (some [directStep])
            | .ok false => do
                match ← Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
                | some searched => pure (some searched)
                | none => pure (some [directStep])
            | .error error => Except.error error) = Except.ok (some steps) at accepted
          cases viable : Detail.coercionEvidenceViable context state direct methods with
          | error error => simp [viable] at accepted
          | ok value =>
            cases value with
            | true =>
              simp only [viable, Except.ok.injEq, Option.some.injEq] at accepted
              subst steps
              intro step member
              cases List.mem_singleton.mp member
              exact directFormed
            | false =>
              simp only [viable] at accepted
              cases searched : Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
              | error error => simp [searched, bind, Except.bind] at accepted
              | ok found =>
                cases found with
                | none =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  intro step member
                  cases List.mem_singleton.mp member
                  exact directFormed
                | some chosen =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  apply searchPaths_formed _ formation profileResult _ searched
                  intro path member
                  cases List.mem_singleton.mp member
                  exact ⟨sourceFormed, by simp⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCoercionIssued
/-! Final normalized formation for the real requirements committed by
expected-type fitting. The normalization extension is the actual continuation
to the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

theorem committed_new_formation
    {semantic : SourceSemantics.Context} {state : State} {outer : Substitution}
    {steps : List Detail.PlannedCoercionStep}
    (stepsFormed : ∀ step ∈ steps, PlannedCoercionStepFormed semantic outer step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  rcases committed_coercion_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · exact primary ▸ (stepsFormed step stepMember).2.2.1
    · exact (stepsFormed step stepMember).2.2.2 row.predicate method

theorem withExpected_new_requirements_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedFormed := expectedFormed expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact fun row member fresh => (fresh member).elim
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            have sourceNormalized : TypeAdmissible semantic (outer.apply (state.resolve actual.type)) :=
              (extension actual.type).symm ▸ actualFormed
            have targetNormalized : TypeAdmissible semantic (outer.apply (state.resolve expected)) :=
              (extension expected).symm ▸ expectedFormed
            exact fun _ member fresh => committed_new_formation
              (coercion_plan_formation formation sourceNormalized targetNormalized planned) member fresh

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation

namespace Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources
open Frontend SourceInference TypeSystem

/-- The actual successful finalizer supplies the normalized producer range.
Its static declaration scope is shared with the semantic initializer context. -/
theorem normalizedCoercionContext
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {state : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn state roots finalized)
    {semantic : SourceSemantics.Context}
    (formation : SourceInferenceRequirementFormation.CoercionFormationContext semantic wholeContext)
    (binders : TypeParameterBindersWellFormed semantic)
    (parameters : semantic.typeParameters = wholeContext.typeParameters)
    (owner : semantic.currentDeclaration = some wholeContext.scope.genericOwner) :
    SourceInferenceNormalizedCoercionFormation.FormationContext semantic wholeContext finalized.substitution :=
  { toCoercionFormationContext := formation
    range := InferenceSubstitutionRangeFormationValidated.rangeAdmissible resources.range_formation
      binders formation.signatures parameters owner formation.residual }

end Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceFinalizedProducerFormation
/-! Producer formation from the actual selected finalizer's validated type
rows and substitution. These facts precede expression/body typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

/-- The static declaration fields shared by an initializer and its successful
whole-body finalizer. Lexical variables and local qualified assumptions may
grow when entering a generalized initializer. -/
structure ProducerScope (whole : SourceInference.Context)
    (semantic : SourceSemantics.Context) : Prop where
  binders : TypeParameterBindersWellFormed semantic
  signatures : semantic.signatures = whole.signatures
  parameters : semantic.typeParameters = whole.typeParameters
  owner : semantic.currentDeclaration = some whole.scope.genericOwner
  residual : semantic.residualTypeVariables = true
  catalog : SignatureCatalogWellFormed semantic.signatures

namespace FinalInferenceResources
variable {whole : SourceInference.Context} {wholeReturn : Ty}
    {evidence : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {semantic : SourceSemantics.Context}

theorem producerRange (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic) :
    SubstitutionRangeAdmissible semantic finalized.substitution :=
  InferenceSubstitutionRangeFormationValidated.rangeAdmissible resources.range_formation
    scope.binders scope.signatures scope.parameters scope.owner scope.residual

/-- The real raw node-type validation and final range validation form the
operand's final type without a semantic typing judgment for that node. -/
theorem retainedProducerType
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {node : ExpressionNode}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes) :
    TypeAdmissible semantic (finalized.substitution.apply node.type) :=
  type_applySubstitution_residual scope.residual (resources.producerRange scope)
    (InferenceTypeFormationValidated.typeAdmissible
      (resources.expressionTypeFormationValidated member)
      scope.binders scope.signatures scope.parameters scope.owner scope.residual)

theorem retainedResolvedProducerType
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {node : ExpressionNode} {state : State}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes)
    (continuation : finalized.substitution.SemanticallyExtends state.inference.substitution) :
    TypeAdmissible semantic (finalized.substitution.apply (state.resolve node.type)) :=
  (continuation node.type).symm ▸ resources.retainedProducerType scope member

/-- Signature obligations follow their accepted declaration attempt. Their
normalization uses the actual selected finalizer's validated range. -/
theorem functionProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {context : SourceInference.Context} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    (member : signature ∈ semantic.signatures.functions)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature =
      .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      (signature.scheme.instantiate state.inference.next).predicates result.signatureRequirements ∧
      ∀ predicate ∈ (signature.scheme.instantiate state.inference.next).predicates,
        PredicateAdmissible semantic
          (TypedTraitResolution.applySubstitution finalized.substitution predicate) := by
  have actual := candidate_signature_issuance scope.catalog scope.binders scope.residual member accepted
  exact ⟨actual.1, fun predicate member =>
    predicate_applySubstitution_residual scope.residual (resources.producerRange scope) (actual.2 predicate member)⟩

/-- The literal requirement refers to its actual allocator variable. Its
final type is obtained from the finalizer's checked literal-origin ledger. -/
theorem integerLiteralProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {origin : IntegerLiteralOrigin} (member : origin ∈ evidence.integerLiterals) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution finalized.substitution
      (ProgramSignatures.builtinIntPredicate (.variable origin.metavariable))) := by
  apply builtin_integer_predicate
  change TypeAdmissible semantic (finalized.substitution.apply (.variable origin.metavariable))
  rcases resources.integer_literal_target_supported origin member with word | integer
  · rw [word]; exact .word scope.binders
  · rw [integer]; exact .integer scope.binders

theorem integerPatternProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {origin : IntegerPatternOrigin} (member : origin ∈ evidence.integerPatterns) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution finalized.substitution
      (ProgramSignatures.builtinIntPredicate (.variable origin.metavariable))) := by
  apply builtin_integer_predicate
  change TypeAdmissible semantic (finalized.substitution.apply (.variable origin.metavariable))
  rcases resources.integer_pattern_target_supported origin member with word | integer
  · rw [word]; exact .word scope.binders
  · rw [integer]; exact .integer scope.binders

/-- A real retained operand supplies the normalized type required by actual
operator-profile issuance. No operator-expression typing is assumed. -/
theorem operatorProducer
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    (scope : ProducerScope whole semantic)
    {context : SourceInference.Context} {state : State} {node : ExpressionNode}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (member : Node.expression node ∈ (evidence.toTypedSource roots).nodes)
    (continuation : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (signatures : context.signatures = whole.signatures)
    (traitNameEq : (context.signatures.trait? trait).map (·.name) = some traitName)
    (accepted : Detail.operatorTraitPredicates context trait methodName (state.resolve node.type)
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible semantic
      (TypedTraitResolution.applySubstitution finalized.substitution predicate) :=
  operator_issuance_normalized scope.catalog (scope.signatures.trans signatures.symm)
    traitNameEq (resources.retainedResolvedProducerType scope member continuation) accepted

end FinalInferenceResources
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRetainedRequirementFormation
/-! Actual issuance and finalizer continuation for retained qualified requirements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

private theorem row_eq_of_unique_ids
    {rows : List Requirement}
    (unique : (rows.map (fun row => row.id.index)).Nodup)
    {left right : Requirement} (leftMember : left ∈ rows)
    (rightMember : right ∈ rows) (same : left.id = right.id) : left = right := by
  induction rows generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨right, rightMember, congrArg RequirementId.index same.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨left, leftMember, congrArg RequirementId.index same⟩))
        · exact induction unique.2 leftMember rightMember same

/-- A retained identity selects the producer's exact row because the actual
ledger has unique allocation identities. Merely sharing an ID without this
ledger invariant would not establish predicate formation. -/
theorem retained_issued_row_formed
    {context : SourceSemantics.Context} {state : State}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (wellFormed : state.RequirementsWellFormed)
    (correspondence : RequirementPredicatesCorrespond state.requirements predicates ids)
    (formed : ∀ predicate ∈ predicates, PredicateAdmissible context predicate)
    {row : Requirement} (member : row ∈ state.requirements) (selected : row.id ∈ ids) :
    PredicateAdmissible context row.predicate := by
  obtain ⟨predicate, issuedMember, predicateFormed⟩ :=
    issued_identity_formed correspondence formed selected
  have unique : (state.requirements.map (fun row => row.id.index)).Nodup := by
    rw [show state.requirements.map (fun row => row.id.index) =
      List.range state.nextRequirement from wellFormed]
    exact List.nodup_range
  have same := row_eq_of_unique_ids unique member issuedMember rfl
  have predicateEq := congrArg Requirement.predicate same
  exact predicateEq.symm ▸ predicateFormed

/-- Candidate allocation, actual ledger retention and unique IDs establish
formation of every retained row owned by that candidate's signature batch. -/
theorem retained_candidate_row_formed
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression} {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {initial retained : State}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    {context : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (signatureMember : signature ∈ context.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments integerOrigins
      call expected initial signature = .ok (some result))
    (included : result.state.requirements ⊆ retained.requirements)
    (wellFormed : retained.RequirementsWellFormed)
    {row : Requirement} (member : row ∈ retained.requirements)
    (selected : row.id ∈ result.signatureRequirements) :
    PredicateAdmissible context row.predicate := by
  have issuance := candidate_signature_issuance catalog binders residual signatureMember success
  exact retained_issued_row_formed wellFormed (issuance.1.mono included)
    issuance.2 member selected

/-- The actual outer substitution absorbs ready-state normalization. The
finalizer's no-capture fact removes the quantifier restriction, while the
separate semantic-extension premise records the genuine inference continuation. -/
theorem retained_predicate_normalization
    {ready : State} {outer : Substitution} {binder : TypedBinder}
    (continuation : outer.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution (outer.without binder.scheme.quantified)
        (Detail.applyPredicate ready predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  rw [FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
    outer binder.scheme.quantified noCapture.quantified_fresh]
  cases predicate with
  | mk trait subject arguments =>
      simp only [Detail.applyPredicate,
        TypedTraitResolution.applySubstitution, List.map_map]
      congr 1
      · exact continuation subject
      · apply List.map_congr_left
        intro argument _
        exact continuation argument

/-- Finalizer range formation closes one authentic retained issuance. This
requires the real ready-to-final substitution continuation, not a backwards
inference from the final requirement ledger. -/
theorem retained_predicate_formed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state ready : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {context : SourceSemantics.Context} {binder : TypedBinder} {predicate : ProgramPredicate}
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (parameters : context.typeParameters = inferenceContext.typeParameters)
    (owner : context.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : context.residualTypeVariables = true)
    (continuation : result.substitution.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture result.substitution binder)
    (formed : PredicateAdmissible context predicate) :
    PredicateAdmissible context
      (TypedTraitResolution.applySubstitution (result.substitution.without binder.scheme.quantified)
        (Detail.applyPredicate ready predicate)) := by
  rw [retained_predicate_normalization continuation noCapture]
  simpa only [Substitution.without, List.foldl_nil] using
    finalizer_predicate_formation resources binders signatures parameters owner residual formed []

/-- Assemble the existing generalized-initializer interface from the exact
selected raw issuances, actual finalization and actual substitution continuation.
The producer premise is restricted to this binder's retained template IDs. -/
theorem retained_formation_of_issuances
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state ready : State} {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots result)
    {target : SourceSemantics.Context} {binder : TypedBinder}
    (binders : TypeParameterBindersWellFormed
      (localSchemeInitializerContext target (binder.applySubstitution result.substitution)))
    (signatures : target.signatures = inferenceContext.signatures)
    (parameters : target.typeParameters = inferenceContext.typeParameters)
    (owner : target.currentDeclaration = some inferenceContext.scope.genericOwner)
    (residual : target.residualTypeVariables = true)
    (continuation : result.substitution.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture result.substitution binder)
    (issued : ∀ row ∈ ready.requirements, row.id ∈ localSchemeTemplateIds binder →
      PredicateAdmissible
        (localSchemeInitializerContext target (binder.applySubstitution result.substitution))
        row.predicate) :
    RetainedRequirementPredicateFormationAt ready binder result.substitution target := by
  intro row member selected
  exact retained_predicate_formed resources binders signatures parameters owner residual
    continuation noCapture (issued row member selected)

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceLocalReadRequirementFormation
/-! Actual local-reference obligation formation under the final substitution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- An actual lookup reuses the prior binder's final formation certificate.
The shared fresh substitution and finalizer no-capture facts transport every
qualified predicate into this occurrence's residual context. -/
theorem local_read_normalized_predicates
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context
      (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution) :
    ∀ predicate ∈ lookup.predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  let inner := (lookup.binder.scheme.instantiateWithSubstitution
    lookup.allocated.inference.next).substitution
  have unique : lookup.binder.scheme.quantified.Nodup := by
    simpa using scheme.quantified_nodup
  have exactInner : ExactSubstitution inner lookup.binder.scheme.quantified := {
    variables_nodup := unique
    domain_permutation := lookup.binder.scheme.instantiateWithSubstitution_substitution_domain_permutation
      lookup.allocated.inference.next unique
  }
  have normalization (predicate : ProgramPredicate) :
      TypedTraitResolution.applySubstitution outer (Detail.applyPredicate lookup.advanced predicate) =
        TypedTraitResolution.applySubstitution outer predicate := by
    have restricted := FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
      outer lookup.binder.scheme.quantified noCapture.quantified_fresh
    simpa only [restricted] using
      retained_predicate_normalization continuation noCapture predicate
  have normalized : lookup.predicates.map (TypedTraitResolution.applySubstitution outer) =
      (instantiateLocalSchemePredicates inner lookup.binder).map
        (TypedTraitResolution.applySubstitution outer) := by
    unfold LocalReadEvents.Lookup.predicates instantiateLocalSchemePredicates
    simp only [List.map_map]
    apply List.map_congr_left
    intro requirement _
    exact normalization _
  have commutes :=
    FlexibleSubstitution.instantiateLocalSchemePredicates_applySubstitution_of_rangeAvoidsVariablesOn
      exactInner noCapture.quantified_fresh
      (localBinderInstantiationNoCapture_predicateRangeAvoids noCapture)
  have composedRange :=
    FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
      lookup.binder.scheme lookup.allocated.inference.next binders residual range
  intro predicate member
  have normalizedMember : TypedTraitResolution.applySubstitution outer predicate ∈
      instantiateLocalSchemePredicates (FlexibleSubstitution.Substitution.mapRange outer inner)
        (lookup.binder.applySubstitution outer) := by
    rw [← commutes, ← normalized]
    exact List.mem_map.mpr ⟨predicate, member, rfl⟩
  obtain ⟨requirement, requirementMember, same⟩ := List.mem_map.mp normalizedMember
  rw [← same]
  exact predicate_applySubstitution_residual residual composedRange
    (predicate_transport_residual
      (source := localSchemeInitializerContext context (lookup.binder.applySubstitution outer)) binders rfl rfl rfl residual
      (formation.entries requirement requirementMember).predicate)

/-- The accepted local-reference branch supplies the exact ledger identities;
formation comes from the same lookup's canonical instantiation, never from
assuming that a solved requirement is well formed. -/
theorem local_read_issuance
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context
      (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution) :
    RequirementPredicatesCorrespond lookup.result.2.requirements lookup.predicates lookup.batch.1 ∧
      (∀ predicate ∈ lookup.predicates,
        PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate)) := by
  have issued := Detail.inferExprFuel_localIdentifier_operational lookup.form lookup.allocation
    lookup.found lookup.accepted lookup.wellFormed lookup.directAllocated
  exact ⟨issued.1, local_read_normalized_predicates lookup binders residual range
    formation scheme noCapture continuation⟩

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedOperatorIssuance
/-! Every obligation issued by the actual unary and binary operator paths is
formed after the same final substitution, including expected-type unification. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

private theorem batch_inference (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference = state.inference := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates ih => exact ih (state.addRequirementWithId predicate).2

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

private theorem actual_operator_predicates
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {trait : Resolved.DeclarationId} {methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply operand))
    (accepted : Detail.operatorTraitPredicates context trait methodName operand parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateAdmissible semantic
      (TypedTraitResolution.applySubstitution outer predicate) := by
  cases found : context.signatures.trait? trait with
  | none => simp [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      bind, Except.bind] at accepted
  | some signature =>
    exact operator_issuance_normalized (traitName := signature.name) catalog signatures (by simp [found]) operandFormed accepted

private abbrev finishOperator (context : SourceInference.Context) (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty) (parameterTypes : List Ty)
    (hasOpenLiteralOperand : Bool) (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure {type := builtinResult, requirements := [], state}
  else
    match dispatch with
    | .function name =>
      if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
          Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
        pure {type := resultType, requirements := [], state}
      else throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
      match ← Detail.operatorTrait? context traitName with
      | some trait =>
        let predicates ← Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType]
        let (requirements,state) := state.addRequirementsWithIds predicates
        pure {type := resultType, requirements, state}
      | none =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
          pure {type := resultType, requirements := [], state}
        else throw (.operatorNotSupported traitName operand)

private theorem finishOperator_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {dispatch : Detail.OperatorDispatch} {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : outer.SemanticallyExtends state.inference.substitution →
      TypeAdmissible semantic (outer.apply operand))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes openLiteral state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact fun _ member fresh => (fresh member).elim
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact fun _ member fresh => (fresh member).elim
      · cases accepted
    | traitMethod traitName methodName =>
      cases traitResult : Detail.operatorTrait? context traitName with
      | error error => simp [traitResult, bind, Except.bind] at accepted
      | ok option =>
        cases option with
        | none =>
          simp only [traitResult, bind, Except.bind] at accepted
          split at accepted
          · cases Except.ok.inj accepted
            exact fun _ member fresh => (fresh member).elim
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have extension : outer.SemanticallyExtends state.inference.substitution := by
              simpa only [batch_inference] using continuation
            intro row member fresh
            rcases batch_origin state predicates member with old | issued
            · exact (fresh old).elim
            · exact actual_operator_predicates catalog signatures (operandFormed extension) predicatesResult
                row.predicate issued

private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (openLiteral : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] openLiteral state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (openLiteral : Bool) (state : State) :
    Except SourceInference.Error Detail.OperatorInferenceResult :=
  let operand := state.resolve operandType
  if Detail.fixedWordOperator operator operand then
    pure {
      type := if Detail.binaryResultIsBool operator then .bool else operand
      requirements := []
      state
    }
  else
    let builtin := Detail.binaryBuiltinType operator
    finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
      (if Detail.binaryResultIsBool operator then .bool else builtin)
      (if Detail.binaryResultIsBool operator then .bool else operand)
      [operand,operand] openLiteral state

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The final continuation normalizes the actual operator operand after any
successful expected-type unification. No intermediate unifier range or
operator-expression typing premise is required. -/
theorem inferUnaryOperator_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {operator : Syntax.UnaryOp} {operandType : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply operandType))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have finish {before : State} {openLiteral : Bool}
      (accepted : finishUnary context operator operandType openLiteral before = .ok result) :
      ∀ row ∈ result.state.requirements, row ∉ before.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) :=
    finishOperator_formation catalog signatures
      (fun extension => (extension operandType).symm ▸ operandFormed) continuation accepted
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finish accepted
  | some expectedType =>
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finish accepted
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        simpa only [unify_requirements unified] using finish accepted

/-- Both real binary unifications precede the same actual trait issuance;
requirements are transported through their unchanged ledger fields. -/
theorem inferBinaryOperator_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed semantic.signatures)
    (signatures : semantic.signatures = context.signatures)
    (operandFormed : TypeAdmissible semantic (outer.apply left))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have finish {before : State} {openLiteral : Bool}
      (accepted : finishBinary context operator left openLiteral before = .ok result) :
      ∀ row ∈ result.state.requirements, row ∉ before.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
    simp only [finishBinary] at accepted
    split at accepted
    · intro row member fresh
      rw [← Except.ok.inj accepted] at member
      exact absurd member fresh
    · exact finishOperator_formation catalog signatures
        (fun extension => (extension left).symm ▸ operandFormed) continuation accepted
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  by_cases shift : Detail.isShiftOperator operator = true
  · obtain ⟨_, _, valued, valueResult, amountResult⟩ :=
      Detail.inferBinaryOperator_shift_result shift accepted
    intro row member fresh
    rw [unify_requirements amountResult, unify_requirements valueResult] at member
    exact absurd member fresh
  by_cases unchecked : Detail.isUncheckedOperator operator = true
  · obtain ⟨unifiedState, prepared, unified, prepare, tailSuccess⟩ :=
      Detail.inferBinaryOperator_unchecked_result unchecked accepted
    have tail := finish (show finishBinary context operator left false prepared = .ok result
      from tailSuccess)
    rcases prepare with rfl | wordResult
    · simpa only [unify_requirements unified] using tail
    · simpa only [unify_requirements unified, unify_requirements wordResult] using tail
  unfold Detail.inferBinaryOperator Detail.binaryOperatorTail at accepted
  rw [if_neg shift, if_neg unchecked] at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    rw [← unify_requirements unified]
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finish accepted
    | some expectedType =>
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finish accepted
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          simpa only [unify_requirements fitted] using finish accepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedExpectedFormation
/-! Actual expected fitting and its recording wrapper form their result and
new obligations under the selected final continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

theorem withExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    TypeAdmissible semantic (outer.apply result.expression.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  rcases Detail.withExpected_success_cases accepted with simple | coerced
  · refine ⟨?_, ?_⟩
    · rw [← simple.2.2]
      exact (continuation actual.type).symm ▸ actualFormed
    · intro row member fresh
      exact (fresh (simple.2.1 ▸ member)).elim
  · obtain ⟨expectedType, plan, expectedEq, planned, resultEq⟩ := coerced
    subst result
    have extension : outer.SemanticallyExtends state.inference.substitution := by
      intro type
      have eq := continuation type
      change outer.apply ((Detail.commitCoercionPlan state plan).2.resolve type) =
        outer.apply type at eq
      rw [Detail.commitCoercionPlan_resolve] at eq
      exact eq
    have target := expectedFormed expectedType (by simp [expectedEq])
    refine ⟨(extension expectedType).symm ▸ target, ?_⟩
    exact withExpected_new_requirements_formation formation extension actualFormed expectedFormed accepted

theorem candidateWithExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    TypeAdmissible semantic (outer.apply result.expression.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  exact withExpected_normalized_formation formation continuation actualFormed expectedFormed
    (Detail.candidateWithExpected_some_withExpected accepted)

theorem recordExpressionWithExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  unfold Detail.recordExpressionWithExpected at accepted
  cases fitted : Detail.withExpected context state {id, type} expected with
  | error error => simp [fitted, bind, Except.bind] at accepted
  | ok fit =>
    simp only [fitted, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    exact withExpected_normalized_formation formation continuation actualFormed expectedFormed fitted

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedArgumentFormation
/-! Requirement formation along the actual ordered argument-fitting trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem

/-- Both batches are interpreted by one final substitution. Actual ledger
membership selects which accepted step issued a newly retained row. -/
theorem new_normalized_requirements_trans
    {semantic : SourceSemantics.Context} {outer : Substitution} {before middle after : State}
    (first : ∀ row ∈ middle.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate))
    (second : ∀ row ∈ after.requirements, row ∉ middle.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  intro row member fresh
  by_cases previous : row ∈ middle.requirements
  · exact first row previous fresh
  · exact second row member previous

/-- Continuation to the selected finalizer is recovered at each actual fit
from the remaining accepted argument trace and its inference progress. -/
theorem argumentFitTrace_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type)) →
    (∀ parameter ∈ parameters, TypeAdmissible semantic (outer.apply parameter)) →
    outer.SemanticallyExtends result.state.inference.substitution →
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  induction trace with
  | nil state =>
    exact fun _ _ _ _ _ _ _ member fresh => (fresh member).elim
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsFormed parametersFormed continuation
    have expectedBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersBelow parameter (by simp)
    have fittedProperties := Detail.candidateWithExpected_some_inferenceProperties ready
      (argumentsBelow argument (by simp)) expectedBelow head
    have tailArgumentsBelow : ∀ arg ∈ arguments, arg.type.VariablesBelow fitted.state.inference.next := by
      intro arg member
      exact (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fittedProperties.1.next_le
    have tailParametersBelow : ∀ type ∈ parameters, type.VariablesBelow fitted.state.inference.next := by
      intro type member
      exact (parametersBelow type (List.mem_cons_of_mem _ member)).weaken fittedProperties.1.next_le
    have tailProperties := rest.inferenceProperties fittedProperties.2.1 tailArgumentsBelow tailParametersBelow
    have fittedContinuation : outer.SemanticallyExtends fitted.state.inference.substitution :=
      continuation.trans tailProperties.1.substitution_extends
    have expectedFormed : ∀ type ∈ some parameter, TypeAdmissible semantic (outer.apply type) := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersFormed parameter (by simp)
    have headFormation := candidateWithExpected_normalized_formation formation fittedContinuation
      (argumentsFormed argument (by simp)) expectedFormed head
    have tailFormation := ih fittedProperties.2.1 tailArgumentsBelow tailParametersBelow
      (fun arg member => argumentsFormed arg (List.mem_cons_of_mem _ member))
      (fun type member => parametersFormed type (List.mem_cons_of_mem _ member)) continuation
    exact new_normalized_requirements_trans headFormation.2 tailFormation

/-- The executable argument pass supplies the trace used above. -/
theorem fitArguments_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (formation : FormationContext semantic context outer)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (parametersFormed : ∀ parameter ∈ parameters, TypeAdmissible semantic (outer.apply parameter))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) :=
  argumentFitTrace_normalized_issuance formation (Detail.fitArguments_some_trace accepted)
    ready argumentsBelow parametersBelow argumentsFormed parametersFormed continuation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedApplicationFormation
/-! Normalized formation follows the actual exposed-function and fresh-result
branches of indirect application. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) : type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The real call reveals both successful fits. Actual inference progress
places each fit under the final continuation; a fresh result is formed from
the finalizer's range rather than an assumed unification formation law. -/
theorem applyFunctionType_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {call : ExpressionId} {callee : Ty} {arguments : List InferredExpression}
    {expected : Option Ty} {state : State} {result : Detail.IndirectApplicationResult}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (ready : state.InferenceReady)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeFormed : TypeAdmissible semantic (outer.apply callee))
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.result.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have productBelow : (Ty.productMany (arguments.map InferredExpression.type)).VariablesBelow state.inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsBelow arg argMember
  have productFormed : TypeAdmissible semantic (outer.apply (Ty.productMany (arguments.map InferredExpression.type))) := by
    rw [FlexibleSubstitution.apply_productMany]
    apply TypeAdmissible.productMany binders
    intro type member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp originalMember
    exact argumentsFormed argument argumentMember
  rcases Detail.applyFunctionType_success_facts accepted with existing | inferred
  · obtain ⟨parameter, returnType, fittedArgument, fittedResult, parts, argumentFit, resultFit, resultEq⟩ := existing
    subst result
    have partsBelow := Detail.functionParts?_success_variablesBelow
      (ready.solved.variablesBelow_apply calleeBelow) parts
    have parameterBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact partsBelow.1
    have argumentProgress := Detail.withExpected_inferenceProperties ready productBelow parameterBelow argumentFit
    have resultProgress := Detail.withExpected_inferenceProperties argumentProgress.2.1
      (partsBelow.2.weaken argumentProgress.1.next_le)
      (fun type member => (expectedBelow type member).weaken argumentProgress.1.next_le) resultFit
    have argumentContinuation : outer.SemanticallyExtends fittedArgument.state.inference.substitution :=
      continuation.trans resultProgress.1.substitution_extends
    have entryContinuation : outer.SemanticallyExtends state.inference.substitution :=
      argumentContinuation.trans argumentProgress.1.substitution_extends
    have resolvedFormed : TypeAdmissible semantic (outer.apply (state.resolve callee)) :=
      (entryContinuation callee).symm ▸ calleeFormed
    rw [functionParts_eq parts] at resolvedFormed
    change TypeAdmissible semantic (.function (outer.apply parameter) (outer.apply returnType)) at resolvedFormed
    have parameterFormed : ∀ type ∈ some parameter, TypeAdmissible semantic (outer.apply type) := by
      intro type member
      cases Option.mem_def.mp member
      exact resolvedFormed.function_parameter
    have argumentFormation := withExpected_normalized_formation formation argumentContinuation
      productFormed parameterFormed argumentFit
    have resultFormation := withExpected_normalized_formation formation continuation
      resolvedFormed.function_result expectedFormed resultFit
    exact ⟨resultFormation.1, new_normalized_requirements_trans argumentFormation.2 resultFormation.2⟩
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have returnEq : returnType = .variable ⟨state.inference.next⟩ := by
      have eq := congrArg Prod.fst allocated
      exact eq.symm
    have returnFormed : TypeAdmissible semantic (outer.apply returnType) := by
      rw [returnEq]
      exact type_applySubstitution_residual formation.residual formation.range
        (.variableOfResidual binders formation.residual _)
    have resultFormation := withExpected_normalized_formation formation continuation returnFormed expectedFormed resultFit
    refine ⟨resultFormation.1, ?_⟩
    intro row member fresh
    apply resultFormation.2 row member
    rw [unify_requirements unified]
    have freshEq : freshState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    simpa only [freshEq, State.fresh] using fresh

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end
