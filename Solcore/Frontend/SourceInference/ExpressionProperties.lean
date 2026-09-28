import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.OccurrenceProperties
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.Frontend.SourceInference.StateProperties
import Solcore.Frontend.ProgramSignatureFormationProperties
import Solcore.TypeSystem.InferenceProperties

/-! Declaration-scoped state preservation for source inference traversals. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

/-- Module-local name filtering never invents function signatures outside
the whole-program catalog. -/
theorem localFunctionsNamed_subset_catalog (context : Context) (name : String) :
    localFunctionsNamed context name ⊆ context.signatures.functions := by
  intro signature member
  exact (List.mem_filter.mp member).1

/-- Resolving visible declarations back to function signatures only retains
entries found in the whole-program function catalog. -/
theorem signaturesForDeclarations_subset_catalog (context : Context)
    (declarations : List ProgramDeclaration) :
    signaturesForDeclarations context declarations ⊆
      context.signatures.functions := by
  intro signature member
  simp only [signaturesForDeclarations, List.mem_filterMap] at member
  obtain ⟨declaration, _, found⟩ := member
  exact List.mem_of_find?_eq_some found

/-- Every successful unqualified function lookup returns only cataloged
function signatures, whether it chose the local tier or imported visibility. -/
theorem functionsNamed_success_subset_catalog
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    (success : functionsNamed context name = .ok candidates) :
    candidates ⊆ context.signatures.functions := by
  by_cases localEmpty : localFunctionsNamed context name = []
  · cases imported : buildProgramImports context.environment
      context.scope.currentModule with
    | error errors =>
        simp [functionsNamed, localEmpty, imported] at success
    | ok visibility =>
        simp [functionsNamed, localEmpty, imported] at success
        subst candidates
        exact signaturesForDeclarations_subset_catalog context
          (visibility.valuesNamed name)
  · simp [functionsNamed, localEmpty] at success
    subst candidates
    exact localFunctionsNamed_subset_catalog context name

/-- A successful qualified lookup which resolves to a concrete candidate list
returns only signatures found in the whole-program function catalog.  A known
namespace with no matching value is represented by the empty subset. -/
theorem qualifiedFunctionsNamed_success_subset_catalog
    {context : Context} {namespacePath : List String} {name : String}
    {candidates : List ProgramFunctionSignature}
    (success : qualifiedFunctionsNamed context namespacePath name =
      .ok (some candidates)) :
    candidates ⊆ context.signatures.functions := by
  cases imported : buildProgramImports context.environment
      context.scope.currentModule with
  | error errors =>
      simp [qualifiedFunctionsNamed, imported] at success
  | ok visibility =>
      cases root : visibility.hasNamespaceRoot namespacePath with
      | false =>
          simp [qualifiedFunctionsNamed, imported, root] at success
      | true =>
          cases targets : visibility.namespacePathTargets namespacePath with
          | nil =>
              simp [qualifiedFunctionsNamed, imported, root, targets]
                at success
              subst candidates
              simp
          | cons target rest =>
              cases rest with
              | nil =>
                  simp [qualifiedFunctionsNamed, imported, root, targets]
                    at success
                  subst candidates
                  exact signaturesForDeclarations_subset_catalog context
                    (visibility.valuesInNamespacePathNamed namespacePath name)
              | cons second tail =>
                  simp [qualifiedFunctionsNamed, imported, root, targets]
                    at success

namespace PlannedCoercionStep

/-- A planned coercion edge retains the canonical `Coerce<source, target>`
obligation and exactly the predicates obtained by instantiating the selected
named coercion method profile at those endpoints. -/
structure ProfileConsistent (trait : Resolved.DeclarationId)
    (profile : CoercionMethodProfile) (step : PlannedCoercionStep) : Prop where
  predicate_eq : step.predicate = {
    trait := .declaration trait
    subject := step.source
    arguments := [step.target]
  }
  methodPredicates_eq :
    coercionMethodPredicates (some profile) step.source step.target =
      .ok step.methodPredicates

end PlannedCoercionStep

private structure CoercionEdgeProfileConsistent
    (trait : Resolved.DeclarationId) (profile : CoercionMethodProfile)
    (edge : CoercionEdge) : Prop where
  predicate_eq : edge.predicate = {
    trait := .declaration trait
    subject := edge.source
    arguments := [edge.target]
  }
  methodPredicates_eq :
    coercionMethodPredicates (some profile) edge.source edge.target =
      .ok edge.methodPredicates

private theorem plannedCoercionPath_isValid_cons_iff
    (source target : Ty) (step : PlannedCoercionStep)
    (rest : List PlannedCoercionStep) :
    PlannedCoercionPath.isValid source target (step :: rest) = true ↔
      step.source = source ∧
        PlannedCoercionPath.isValid step.target target rest = true := by
  cases rest <;>
    simp [PlannedCoercionPath.isValid, Bool.and_eq_true, beq_iff_eq]

private theorem plannedCoercionPath_isValid_append
    {source current : Ty} {steps : List PlannedCoercionStep}
    (valid : PlannedCoercionPath.isValid source current steps = true)
    (step : PlannedCoercionStep) (source_eq : step.source = current) :
    PlannedCoercionPath.isValid source step.target (steps ++ [step]) = true := by
  induction steps generalizing source with
  | nil =>
      simp [PlannedCoercionPath.isValid, beq_iff_eq] at valid ⊢
      exact source_eq.trans valid.symm
  | cons head rest induction =>
      have parts := (plannedCoercionPath_isValid_cons_iff
        source current head rest).mp valid
      apply (plannedCoercionPath_isValid_cons_iff source step.target head
        (rest ++ [step])).mpr
      exact ⟨parts.1, induction parts.2⟩

private theorem coercionRuleEdge?_some_source
    {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : CoercionEdge}
    (success : coercionRuleEdge? trait source rule = some edge) :
    edge.source = source := by
  by_cases traitMismatch :
      (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [coercionRuleEdge?, traitMismatch] at success
  · simp only [coercionRuleEdge?, traitMismatch, ↓reduceIte] at success
    cases arguments : (TypedTraitResolution.freshenRuleFor rule {
        trait := ProgramTraitId.declaration trait
        subject := source
        arguments := [source]
      }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at success
    | cons target rest =>
        cases rest with
        | cons second tail => simp [arguments, bind, Option.bind] at success
        | nil =>
            simp only [arguments, bind, Option.bind] at success
            cases unified : (Unification.unify [{
                left := (TypedTraitResolution.freshenRuleFor rule {
                  trait := ProgramTraitId.declaration trait
                  subject := source
                  arguments := [source]
                }).head.subject
                right := source
              }]).toOption with
            | none => simp [unified] at success
            | some substitution =>
                simp only [unified, Option.bind_some] at success
                by_cases blocked :
                    substitution.domain.any source.freeVariables.contains = true
                · simp [blocked] at success
                · by_cases ground :
                      isGroundCoercionTarget
                        (substitution.apply target) = true
                  · simp [blocked, ground] at success
                    subst edge
                    rfl
                  · simp [blocked, ground] at success

private theorem coercionRuleEdge?_some_predicate
    {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : CoercionEdge}
    (success : coercionRuleEdge? trait source rule = some edge) :
    edge.predicate = {
      trait := .declaration trait
      subject := edge.source
      arguments := [edge.target]
    } := by
  by_cases traitMismatch :
      (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [coercionRuleEdge?, traitMismatch] at success
  · simp only [coercionRuleEdge?, traitMismatch, ↓reduceIte] at success
    cases arguments : (TypedTraitResolution.freshenRuleFor rule {
        trait := ProgramTraitId.declaration trait
        subject := source
        arguments := [source]
      }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at success
    | cons target rest =>
        cases rest with
        | cons second tail => simp [arguments, bind, Option.bind] at success
        | nil =>
            simp only [arguments, bind, Option.bind] at success
            cases unified : (Unification.unify [{
                left := (TypedTraitResolution.freshenRuleFor rule {
                  trait := ProgramTraitId.declaration trait
                  subject := source
                  arguments := [source]
                }).head.subject
                right := source
              }]).toOption with
            | none => simp [unified] at success
            | some substitution =>
                simp only [unified, Option.bind_some] at success
                by_cases blocked :
                    substitution.domain.any source.freeVariables.contains = true
                · simp [blocked] at success
                · by_cases ground :
                      isGroundCoercionTarget
                        (substitution.apply target) = true
                  · simp [blocked, ground] at success
                    subst edge
                    rfl
                  · simp [blocked, ground] at success

private theorem programTraitId_bne_eq_false_iff_eq
    (left right : ProgramTraitId) :
    (left != right) = false ↔ left = right := by
  change (!instBEqProgramTraitId.beq left right) = false ↔ left = right
  cases left <;> cases right <;>
    simp [instBEqProgramTraitId.beq, instBEqBuiltinTraitId.beq]
  case builtin.builtin left right =>
    cases left
    cases right
    rfl

private theorem programTraitId_bne_eq_true_iff_ne
    (left right : ProgramTraitId) :
    (left != right) = true ↔ left ≠ right := by
  change (!instBEqProgramTraitId.beq left right) = true ↔ left ≠ right
  cases left <;> cases right <;>
    simp [instBEqProgramTraitId.beq, instBEqBuiltinTraitId.beq]
  case builtin.builtin left right =>
    cases left
    cases right
    rfl

private theorem programPredicate_eq
    {left right : ProgramPredicate}
    (trait_eq : left.trait = right.trait)
    (subject_eq : left.subject = right.subject)
    (arguments_eq : left.arguments = right.arguments) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem assumptionCoercionEdges_member_source
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈ assumptionCoercionEdges context state trait source) :
    edge.source = source := by
  unfold assumptionCoercionEdges at member
  simp only [List.mem_filterMap] at member
  obtain ⟨assumption, _, produced⟩ := member
  simp only [Bool.or_eq_true, programTraitId_bne_eq_true_iff_ne,
    bne_iff_ne] at produced
  grind

private theorem assumptionCoercionEdges_member_predicate
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈ assumptionCoercionEdges context state trait source) :
    edge.predicate = {
      trait := .declaration trait
      subject := edge.source
      arguments := [edge.target]
    } := by
  unfold assumptionCoercionEdges at member
  simp only [List.mem_filterMap] at member
  obtain ⟨assumption, _, produced⟩ := member
  simp only [Bool.or_eq_true, programTraitId_bne_eq_true_iff_ne,
    bne_iff_ne] at produced
  apply programPredicate_eq <;> grind

private theorem rawCoercionEdges_member_source
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈
      ((context.signatures.implRules.filterMap
        (coercionRuleEdge? trait source)) ++
        assumptionCoercionEdges context state trait source).eraseDups) :
    edge.source = source := by
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with ruleMember | assumptionMember
  · simp only [List.mem_filterMap] at ruleMember
    obtain ⟨rule, _, produced⟩ := ruleMember
    exact coercionRuleEdge?_some_source produced
  · exact assumptionCoercionEdges_member_source assumptionMember

private theorem rawCoercionEdges_member_predicate
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈
      ((context.signatures.implRules.filterMap
        (coercionRuleEdge? trait source)) ++
        assumptionCoercionEdges context state trait source).eraseDups) :
    edge.predicate = {
      trait := .declaration trait
      subject := edge.source
      arguments := [edge.target]
    } := by
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with ruleMember | assumptionMember
  · simp only [List.mem_filterMap] at ruleMember
    obtain ⟨rule, _, produced⟩ := ruleMember
    exact coercionRuleEdge?_some_predicate produced
  · exact assumptionCoercionEdges_member_predicate assumptionMember

private def attachCoercionMethodPredicates
    (profile : Option CoercionMethodProfile) (edge : CoercionEdge) :
    Except Error CoercionEdge := do
  let methodPredicates ←
    coercionMethodPredicates profile edge.source edge.target
  pure { edge with methodPredicates }

private theorem mapCoercionMethodPredicates_success_sources
    (profile : Option CoercionMethodProfile) (source : Ty) :
    ∀ (input output : List CoercionEdge),
      (∀ (edge : CoercionEdge), edge ∈ input → edge.source = source) →
      input.mapM (attachCoercionMethodPredicates profile) = .ok output →
      ∀ (edge : CoercionEdge), edge ∈ output → edge.source = source := by
  intro input
  induction input with
  | nil =>
      intro output _ success
      change Except.ok [] = Except.ok output at success
      injection success with outputEq
      subst output
      simp
  | cons head rest induction =>
      intro output inputSources success
      cases methodResult :
          coercionMethodPredicates profile head.source head.target with
      | error error =>
          simp [List.mapM_cons, attachCoercionMethodPredicates, methodResult,
            bind, Except.bind, pure, Pure.pure, Except.pure] at success
      | ok methodPredicates =>
          simp only [List.mapM_cons, attachCoercionMethodPredicates,
            methodResult, bind, Except.bind, pure, Pure.pure, Except.pure]
            at success
          cases tailResult : rest.mapM
              (attachCoercionMethodPredicates profile) with
          | error error =>
              rw [tailResult] at success
              contradiction
          | ok tail =>
              rw [tailResult] at success
              injection success with outputEq
              subst output
              intro edge member
              rcases List.mem_cons.mp member with rfl | member
              · exact inputSources head (by simp)
              · exact induction tail
                  (fun candidate candidateMember =>
                    inputSources candidate (by simp [candidateMember]))
                  tailResult edge member

private theorem mapCoercionMethodPredicates_success_profileConsistent
    (trait : Resolved.DeclarationId) (profile : CoercionMethodProfile) :
    ∀ (input output : List CoercionEdge),
      (∀ (edge : CoercionEdge), edge ∈ input → edge.predicate = {
        trait := .declaration trait
        subject := edge.source
        arguments := [edge.target]
      }) →
      input.mapM (attachCoercionMethodPredicates (some profile)) =
        .ok output →
      ∀ (edge : CoercionEdge), edge ∈ output →
        CoercionEdgeProfileConsistent trait profile edge := by
  intro input
  induction input with
  | nil =>
      intro output _ success
      change Except.ok [] = Except.ok output at success
      injection success with outputEq
      subst output
      simp
  | cons head rest induction =>
      intro output inputPredicates success
      cases methodResult :
          coercionMethodPredicates (some profile) head.source head.target with
      | error error =>
          simp [List.mapM_cons, attachCoercionMethodPredicates, methodResult,
            bind, Except.bind, pure, Pure.pure, Except.pure] at success
      | ok methodPredicates =>
          simp only [List.mapM_cons, attachCoercionMethodPredicates,
            methodResult, bind, Except.bind, pure, Pure.pure, Except.pure]
            at success
          cases tailResult : rest.mapM
              (attachCoercionMethodPredicates (some profile)) with
          | error error =>
              rw [tailResult] at success
              contradiction
          | ok tail =>
              rw [tailResult] at success
              injection success with outputEq
              subst output
              intro edge member
              rcases List.mem_cons.mp member with rfl | member
              · exact {
                  predicate_eq := inputPredicates head (by simp)
                  methodPredicates_eq := methodResult
                }
              · exact induction tail
                  (fun candidate candidateMember =>
                    inputPredicates candidate (by simp [candidateMember]))
                  tailResult edge member

private theorem coercionEdges_success_sources
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {edges : List CoercionEdge}
    (success : coercionEdges context state profile trait source = .ok edges) :
    ∀ edge, edge ∈ edges → edge.source = source := by
  unfold coercionEdges at success
  let input :=
    ((context.signatures.implRules.filterMap
      (coercionRuleEdge? trait source)) ++
      assumptionCoercionEdges context state trait source).eraseDups
  change input.mapM (attachCoercionMethodPredicates profile) = .ok edges
    at success
  exact mapCoercionMethodPredicates_success_sources profile source input
    edges (fun edge member => by
      exact rawCoercionEdges_member_source (by simpa [input] using member))
    success

private theorem coercionEdges_success_profileConsistent
    {context : Context} {state : State}
    {profile : CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {edges : List CoercionEdge}
    (success : coercionEdges context state (some profile) trait source =
      .ok edges) :
    ∀ edge, edge ∈ edges →
      CoercionEdgeProfileConsistent trait profile edge := by
  unfold coercionEdges at success
  let input :=
    ((context.signatures.implRules.filterMap
      (coercionRuleEdge? trait source)) ++
      assumptionCoercionEdges context state trait source).eraseDups
  change input.mapM (attachCoercionMethodPredicates (some profile)) =
    .ok edges at success
  exact mapCoercionMethodPredicates_success_profileConsistent trait profile
    input edges (fun edge member => by
      exact rawCoercionEdges_member_predicate
        (by simpa [input] using member)) success

private theorem viableCoercionEdges_viable_subset
    (context : Context) (state : State) (edges : List CoercionEdge) :
    (viableCoercionEdges context state edges).viable ⊆ edges := by
  intro edge member
  induction edges with
  | nil => simp [viableCoercionEdges] at member
  | cons head rest induction =>
      simp only [viableCoercionEdges] at member
      cases result : coercionEvidenceViable context state head.predicate
          head.methodPredicates with
      | error error =>
          simp [result] at member
          exact List.mem_cons_of_mem head (induction member)
      | ok viable =>
          cases viable with
          | false =>
              simp [result] at member
              exact List.mem_cons_of_mem head (induction member)
          | true =>
              simp [result] at member
              rcases member with rfl | member
              · simp
              · exact List.mem_cons_of_mem head (induction member)

private theorem plannedCoercionStep_profileConsistent_of_edge
    {trait : Resolved.DeclarationId} {profile : CoercionMethodProfile}
    {edge : CoercionEdge}
    (consistent : CoercionEdgeProfileConsistent trait profile edge) :
    PlannedCoercionStep.ProfileConsistent trait profile {
      source := edge.source
      target := edge.target
      predicate := edge.predicate
      methodPredicates := edge.methodPredicates
    } := {
  predicate_eq := consistent.predicate_eq
  methodPredicates_eq := consistent.methodPredicates_eq
}

private theorem expandCoercionPath_success_profileConsistent
    {context : Context} {state : State}
    {profile : CoercionMethodProfile}
    {trait : Resolved.DeclarationId}
    {path : CoercionPath} {expansion : CoercionExpansion}
    (pathConsistent : ∀ step, step ∈ path.steps →
      PlannedCoercionStep.ProfileConsistent trait profile step)
    (success : expandCoercionPath context state (some profile) trait path =
      .ok expansion) :
    ∀ candidate, candidate ∈ expansion.paths →
      ∀ step, step ∈ candidate.steps →
        PlannedCoercionStep.ProfileConsistent trait profile step := by
  unfold expandCoercionPath at success
  cases edgesResult :
      coercionEdges context state (some profile) trait path.current with
  | error error =>
      simp [edgesResult, bind, Except.bind] at success
  | ok allEdges =>
      simp only [edgesResult, bind, Except.bind, pure, Pure.pure, Except.pure]
        at success
      injection success with expansionEq
      subst expansion
      intro candidate member
      simp only [List.mem_map] at member
      obtain ⟨edge, edgeMember, rfl⟩ := member
      intro step stepMember
      rw [List.mem_append] at stepMember
      rcases stepMember with previous | added
      · exact pathConsistent step previous
      · simp only [List.mem_singleton] at added
        subst step
        apply plannedCoercionStep_profileConsistent_of_edge
        exact coercionEdges_success_profileConsistent edgesResult edge
          (List.mem_filter.mp
            (viableCoercionEdges_viable_subset context state _ edgeMember)).1

private theorem expandCoercionPath_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {path : CoercionPath} {expansion : CoercionExpansion}
    (pathValid : PlannedCoercionPath.isValid source path.current
      path.steps = true)
    (success : expandCoercionPath context state profile trait path =
      .ok expansion) :
    ∀ candidate, candidate ∈ expansion.paths →
      PlannedCoercionPath.isValid source candidate.current
        candidate.steps = true := by
  unfold expandCoercionPath at success
  cases edgesResult : coercionEdges context state profile trait path.current with
  | error error =>
      simp [edgesResult, bind, Except.bind] at success
  | ok allEdges =>
      simp only [edgesResult, bind, Except.bind, pure, Pure.pure, Except.pure]
        at success
      injection success with expansionEq
      subst expansion
      intro candidate member
      simp only [List.mem_map] at member
      obtain ⟨edge, edgeMember, rfl⟩ := member
      change PlannedCoercionPath.isValid source edge.target
        (path.steps ++ [{
          source := edge.source
          target := edge.target
          predicate := edge.predicate
          methodPredicates := edge.methodPredicates
        }]) = true
      exact plannedCoercionPath_isValid_append pathValid
        ({
          source := edge.source
          target := edge.target
          predicate := edge.predicate
          methodPredicates := edge.methodPredicates
        } : PlannedCoercionStep)
        (coercionEdges_success_sources edgesResult edge
          (List.mem_filter.mp
            (viableCoercionEdges_viable_subset context state _ edgeMember)).1)

private theorem expandCoercionPaths_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {frontier : List CoercionPath} {expansion : CoercionExpansion}
    (frontierValid : ∀ path, path ∈ frontier →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : expandCoercionPaths context state profile trait frontier =
      .ok expansion) :
    ∀ path, path ∈ expansion.paths →
      PlannedCoercionPath.isValid source path.current path.steps = true := by
  induction frontier generalizing expansion with
  | nil =>
      simp [expandCoercionPaths, pure, Pure.pure, Except.pure] at success
      subst expansion
      simp
  | cons path rest induction =>
      simp only [expandCoercionPaths] at success
      cases headResult : expandCoercionPath context state profile trait path with
      | error error =>
          simp [headResult, bind, Except.bind] at success
      | ok head =>
          cases tailResult : expandCoercionPaths context state profile trait
              rest with
          | error error =>
              simp [headResult, tailResult, bind, Except.bind] at success
          | ok tail =>
              simp [headResult, tailResult, bind, Except.bind, pure,
                Pure.pure, Except.pure] at success
              subst expansion
              intro candidate member
              rw [List.mem_append] at member
              rcases member with headMember | tailMember
              · exact expandCoercionPath_success_valid
                  (frontierValid path (by simp)) headResult candidate headMember
              · exact induction
                  (fun candidate candidateMember =>
                    frontierValid candidate (by simp [candidateMember]))
                  tailResult candidate tailMember

private theorem expandCoercionPaths_success_profileConsistent
    {context : Context} {state : State}
    {profile : CoercionMethodProfile}
    {trait : Resolved.DeclarationId}
    {frontier : List CoercionPath} {expansion : CoercionExpansion}
    (frontierConsistent : ∀ path, path ∈ frontier →
      ∀ step, step ∈ path.steps →
        PlannedCoercionStep.ProfileConsistent trait profile step)
    (success : expandCoercionPaths context state (some profile) trait frontier =
      .ok expansion) :
    ∀ path, path ∈ expansion.paths →
      ∀ step, step ∈ path.steps →
        PlannedCoercionStep.ProfileConsistent trait profile step := by
  induction frontier generalizing expansion with
  | nil =>
      simp [expandCoercionPaths, pure, Pure.pure, Except.pure] at success
      subst expansion
      simp
  | cons path rest induction =>
      simp only [expandCoercionPaths] at success
      cases headResult :
          expandCoercionPath context state (some profile) trait path with
      | error error =>
          simp [headResult, bind, Except.bind] at success
      | ok head =>
          cases tailResult :
              expandCoercionPaths context state (some profile) trait rest with
          | error error =>
              simp [headResult, tailResult, bind, Except.bind] at success
          | ok tail =>
              simp [headResult, tailResult, bind, Except.bind, pure,
                Pure.pure, Except.pure] at success
              subst expansion
              intro candidate member
              rw [List.mem_append] at member
              rcases member with headMember | tailMember
              · exact expandCoercionPath_success_profileConsistent
                  (frontierConsistent path (by simp)) headResult candidate
                  headMember
              · exact induction
                  (fun candidate candidateMember =>
                    frontierConsistent candidate (by simp [candidateMember]))
                  tailResult candidate tailMember

private theorem selectCoercionPath_success_valid
    {source target : Ty} {paths : List CoercionPath}
    {steps : List PlannedCoercionStep}
    (pathsValid : ∀ path, path ∈ paths →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : selectCoercionPath source target paths = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  unfold selectCoercionPath at success
  cases matchingEq :
      (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [matchingEq] at success
  | cons first rest =>
      cases rest with
      | nil =>
          simp [matchingEq] at success
          subst steps
          have firstMember : first ∈
              (paths.filter fun path => path.current == target).eraseDups := by
            rw [matchingEq]
            simp
          rw [List.mem_eraseDups, List.mem_filter] at firstMember
          have currentEq : first.current = target :=
            beq_iff_eq.mp firstMember.2
          subst target
          exact pathsValid first firstMember.1
      | cons second tail => simp [matchingEq] at success

private theorem selectCoercionPath_success_profileConsistent
    {trait : Resolved.DeclarationId} {profile : CoercionMethodProfile}
    {source target : Ty} {paths : List CoercionPath}
    {steps : List PlannedCoercionStep}
    (pathsConsistent : ∀ path, path ∈ paths →
      ∀ step, step ∈ path.steps →
        PlannedCoercionStep.ProfileConsistent trait profile step)
    (success : selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step, step ∈ steps →
      PlannedCoercionStep.ProfileConsistent trait profile step := by
  unfold selectCoercionPath at success
  cases matchingEq :
      (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [matchingEq] at success
  | cons first rest =>
      cases rest with
      | nil =>
          simp [matchingEq] at success
          subst steps
          have firstMember : first ∈
              (paths.filter fun path => path.current == target).eraseDups := by
            rw [matchingEq]
            simp
          rw [List.mem_eraseDups, List.mem_filter] at firstMember
          exact pathsConsistent first firstMember.1
      | cons second tail => simp [matchingEq] at success

private theorem finishCoercionSearch_ne_some
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (success : finishCoercionSearch blocked = .ok (some steps)) : False := by
  unfold finishCoercionSearch at success
  cases blocked <;> simp at success

private theorem searchCoercionPaths_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    {fuel : Nat} {frontier : List CoercionPath}
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (frontierValid : ∀ path, path ∈ frontier →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  induction fuel generalizing frontier blocked steps with
  | zero =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state profile trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok beyond =>
          simp only [expandedResult, bind, Except.bind] at success
          by_cases empty : beyond.paths.isEmpty = true
          · simp only [empty, ↓reduceIte] at success
            exact (finishCoercionSearch_ne_some success).elim
          · simp [empty] at success
  | succ fuel induction =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state profile trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok next =>
          simp only [expandedResult, bind, Except.bind] at success
          have nextValid :=
            expandCoercionPaths_success_valid frontierValid expandedResult
          cases selectedResult : selectCoercionPath source target next.paths with
          | error error =>
              simp [selectedResult, bind, Except.bind] at success
          | ok selected =>
              simp only [selectedResult, bind, Except.bind] at success
              cases selected with
              | some selectedSteps =>
                  simp [pure, Pure.pure, Except.pure] at success
                  subst steps
                  exact selectCoercionPath_success_valid nextValid
                    selectedResult
              | none =>
                  simp only at success
                  by_cases empty : next.paths.isEmpty = true
                  · simp only [empty, ↓reduceIte] at success
                    exact (finishCoercionSearch_ne_some success).elim
                  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
                      at success
                    exact induction nextValid success

private theorem searchCoercionPaths_success_profileConsistent
    {context : Context} {state : State}
    {profile : CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    {fuel : Nat} {frontier : List CoercionPath}
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (frontierConsistent : ∀ path, path ∈ frontier →
      ∀ step, step ∈ path.steps →
        PlannedCoercionStep.ProfileConsistent trait profile step)
    (success : searchCoercionPaths context state (some profile) trait source
      target fuel frontier blocked = .ok (some steps)) :
    ∀ step, step ∈ steps →
      PlannedCoercionStep.ProfileConsistent trait profile step := by
  induction fuel generalizing frontier blocked steps with
  | zero =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state (some profile) trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok beyond =>
          simp only [expandedResult, bind, Except.bind] at success
          by_cases empty : beyond.paths.isEmpty = true
          · simp only [empty, ↓reduceIte] at success
            exact (finishCoercionSearch_ne_some success).elim
          · simp [empty] at success
  | succ fuel induction =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state (some profile) trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok next =>
          simp only [expandedResult, bind, Except.bind] at success
          have nextConsistent :=
            expandCoercionPaths_success_profileConsistent
              frontierConsistent expandedResult
          cases selectedResult : selectCoercionPath source target next.paths with
          | error error =>
              simp [selectedResult, bind, Except.bind] at success
          | ok selected =>
              simp only [selectedResult, bind, Except.bind] at success
              cases selected with
              | some selectedSteps =>
                  simp [pure, Pure.pure, Except.pure] at success
                  subst steps
                  exact selectCoercionPath_success_profileConsistent
                    nextConsistent selectedResult
              | none =>
                  simp only at success
                  by_cases empty : next.paths.isEmpty = true
                  · simp only [empty, ↓reduceIte] at success
                    exact (finishCoercionSearch_ne_some success).elim
                  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
                      at success
                    exact induction nextConsistent success

/-- Every coercion plan returned by source inference has the requested exact
endpoints and pairwise-adjacent planned steps. -/
theorem coercionPlan?_some_isValid
    {context : Context} {state : State} {source target : Ty}
    {steps : List PlannedCoercionStep}
    (success : coercionPlan? context state source target = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  unfold coercionPlan? at success
  cases traitResult : conventionalTraitWithArity? context "Coerce" 2 with
  | error error =>
      simp [traitResult, bind, Except.bind] at success
  | ok traitOption =>
      simp only [traitResult, bind, Except.bind] at success
      cases traitOption with
      | none => simp [pure, Pure.pure, Except.pure] at success
      | some trait =>
          cases profileResult : coercionMethodProfile? context trait with
          | error error =>
              simp [profileResult, bind, Except.bind] at success
          | ok profile =>
              simp only [profileResult, bind, Except.bind] at success
              let direct : ProgramPredicate := {
                trait
                subject := source
                arguments := [target]
              }
              cases methodResult :
                  coercionMethodPredicates profile source target with
              | error error =>
                  simp [methodResult, bind, Except.bind] at success
              | ok methodPredicates =>
                  simp only [methodResult, bind, Except.bind] at success
                  cases viableResult : coercionEvidenceViable context state
                      direct methodPredicates with
                  | error error =>
                      simp [direct, viableResult] at success
                  | ok viable =>
                      cases viable with
                      | true =>
                          simp [direct, viableResult, pure, Pure.pure,
                            Except.pure] at success
                          subst steps
                          simp [PlannedCoercionPath.isValid]
                      | false =>
                          cases searchResult : searchCoercionPaths context state
                              profile trait source target context.coercionDepth
                              [{
                                current := source
                                visited := [source]
                                steps := []
                              }] [] with
                          | error error =>
                              simp [direct, viableResult, searchResult, bind,
                                Except.bind] at success
                          | ok plan =>
                              simp only [direct, viableResult, searchResult,
                                bind, Except.bind] at success
                              cases plan with
                              | none =>
                                  simp [pure, Pure.pure, Except.pure] at success
                                  subst steps
                                  simp [PlannedCoercionPath.isValid]
                              | some searchedSteps =>
                                  simp [pure, Pure.pure, Except.pure] at success
                                  subst steps
                                  exact searchCoercionPaths_success_valid
                                    (by
                                      intro path member
                                      simp at member
                                      subst path
                                      simp [PlannedCoercionPath.isValid])
                                    searchResult

/-- When the conventional `Coerce` trait has a named method profile, every
edge returned by coercion planning carries its canonical primary predicate and
the exact method predicates instantiated for that edge's endpoints. -/
theorem coercionPlan?_some_profileConsistent
    {context : Context} {state : State} {source target : Ty}
    {trait : Resolved.DeclarationId} {profile : CoercionMethodProfile}
    {steps : List PlannedCoercionStep}
    (traitSuccess :
      conventionalTraitWithArity? context "Coerce" 2 = .ok (some trait))
    (profileSuccess :
      coercionMethodProfile? context trait = .ok (some profile))
    (success : coercionPlan? context state source target = .ok (some steps)) :
    ∀ step, step ∈ steps →
      PlannedCoercionStep.ProfileConsistent trait profile step := by
  unfold coercionPlan? at success
  rw [traitSuccess] at success
  simp only [bind, Except.bind] at success
  rw [profileSuccess] at success
  simp only [bind, Except.bind] at success
  let direct : ProgramPredicate := {
    trait := .declaration trait
    subject := source
    arguments := [target]
  }
  cases methodResult :
      coercionMethodPredicates (some profile) source target with
  | error error =>
      simp [methodResult, bind, Except.bind] at success
  | ok methodPredicates =>
      simp only [methodResult, bind, Except.bind] at success
      cases viableResult :
          coercionEvidenceViable context state direct methodPredicates with
      | error error =>
          simp [direct, viableResult] at success
      | ok viable =>
          cases viable with
          | true =>
              simp [direct, viableResult, pure, Pure.pure, Except.pure]
                at success
              subst steps
              intro step member
              simp only [List.mem_singleton] at member
              subst step
              exact {
                predicate_eq := rfl
                methodPredicates_eq := methodResult
              }
          | false =>
              cases searchResult :
                  searchCoercionPaths context state (some profile) trait source
                    target context.coercionDepth [{
                      current := source
                      visited := [source]
                      steps := []
                    }] [] with
              | error error =>
                  simp [direct, viableResult, searchResult, bind,
                    Except.bind] at success
              | ok plan =>
                  simp only [direct, viableResult, searchResult, bind,
                    Except.bind] at success
                  cases plan with
                  | none =>
                      simp [pure, Pure.pure, Except.pure] at success
                      subst steps
                      intro step member
                      simp only [List.mem_singleton] at member
                      subst step
                      exact {
                        predicate_eq := rfl
                        methodPredicates_eq := methodResult
                      }
                  | some searchedSteps =>
                      simp [pure, Pure.pure, Except.pure] at success
                      subst steps
                      exact searchCoercionPaths_success_profileConsistent
                        (by
                          intro path member
                          simp at member
                          subst path
                          simp)
                        searchResult

@[simp] private theorem addRequirementsWithIds_resolve
    (state : State) (predicates : List ProgramPredicate) (type : Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type =
      state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

/-- Allocating coercion requirement identities leaves type resolution
unchanged. -/
@[simp] theorem commitCoercionPlan_resolve
    (state : State) (plan : List PlannedCoercionStep) (type : Ty) :
    (commitCoercionPlan state plan).2.resolve type = state.resolve type := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      exact addRequirementsWithIds_resolve
        (state.addRequirementWithId step.predicate).2
        step.methodPredicates type

/-- Committing a coercion plan leaves type inference unchanged, so it makes
reflexive semantic progress from any solved input state. -/
theorem commitCoercionPlan_inferenceProgress
    (state : State) (plan : List PlannedCoercionStep)
    (solved : state.inference.Solved) :
    state.InferenceProgress (commitCoercionPlan state plan).2 := by
  induction plan generalizing state with
  | nil => exact .refl solved
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      have primaryProgress :=
        State.InferenceProgress.addRequirementWithId
          state step.predicate solved
      have methodsProgress :=
        State.InferenceProgress.addRequirementsWithIds
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates primaryProgress.solved
      exact primaryProgress.trans (methodsProgress.trans
        (induction _ methodsProgress.solved))

/-- Committing a coercion plan preserves inference readiness because it only
allocates requirement identities. -/
theorem commitCoercionPlan_preserves_inferenceReady
    (state : State) (plan : List PlannedCoercionStep)
    (ready : state.InferenceReady) :
    (commitCoercionPlan state plan).2.InferenceReady := by
  induction plan generalizing state with
  | nil => exact ready
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      exact induction _
        (State.InferenceReady.addRequirementsWithIds step.methodPredicates
          (State.InferenceReady.addRequirementWithId step.predicate ready))

/-- Every successful expected-type fit returns either the empty equality path
or a committed coercion path with exact resolved endpoints and adjacency. -/
theorem withExpected_success_coercions_isValid
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    CoercionPath.isValid (result.state.resolve actual.type)
      result.expression.type result.coercions = true := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      simp [CoercionPath.isValid]
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          apply beq_iff_eq.mpr
          exact TypeSystem.InferState.unify_resolve_eq unification
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok planOption =>
                  cases planOption with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      have planValid : PlannedCoercionPath.isValid
                          (state.resolve actual.type) (state.resolve expected)
                          plan = true :=
                        coercionPlan?_some_isValid planResult
                      have committedValid :=
                        commitCoercionPlan_isValid state plan planValid
                      simpa only [commitCoercionPlan_resolve] using
                        committedValid

/-- Invert successful expected-type fitting into the two shapes needed by
semantic consumers.  The no-coercion branch covers both an absent expectation
and successful unification.  The coercion branch exposes the exact plan and
commit result retained by the returned expression. -/
theorem withExpected_success_cases
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    (result.coercions = [] ∧
        result.state.requirements = state.requirements ∧
        result.state.resolve actual.type = result.expression.type) ∨
      ∃ expectedType plan,
        expected = some expectedType ∧
          coercionPlan? context state (state.resolve actual.type)
              (state.resolve expectedType) = .ok (some plan) ∧
            result = {
              expression := {
                actual with type := state.resolve expectedType
              }
              coercions := (commitCoercionPlan state plan).1
              state := (commitCoercionPlan state plan).2
            } := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      exact .inl ⟨rfl, rfl, rfl⟩
  | some expectedType =>
      cases unification : state.inference.unify actual.type expectedType with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          refine .inl ⟨rfl, rfl, ?_⟩
          exact TypeSystem.InferState.unify_resolve_eq unification
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expectedType) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok planOption =>
                  cases planOption with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact .inr ⟨expectedType, plan, rfl, planResult, rfl⟩

/-- A successfully resolved source annotation contains no flexible
metavariables, so it lies below every inference allocator bound. -/
theorem resolveSourceType_success_variablesBelow
    {context : Context} {source : Syntax.TypeExpr} {type : Ty}
    (success : resolveSourceType context source = .ok type)
    (next : Nat) :
    type.VariablesBelow next :=
  (resolveSourceType_success_formation success).variablesBelow next

/-- A successfully resolved source annotation contains no flexible
metavariables, so every inference substitution fixes it. -/
theorem resolveSourceType_success_apply_eq_self
    {context : Context} {source : Syntax.TypeExpr} {type : Ty}
    (substitution : Substitution)
    (success : resolveSourceType context source = .ok type) :
    substitution.apply type = type :=
  (resolveSourceType_success_formation success).apply_eq_self substitution

@[simp] private theorem except_pure_eq_ok {ε α : Type}
    (value result : α) :
    ((pure value : Except ε α) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem except_map_eq_ok {ε α β : Type} {map : α → β}
    {computation : Except ε α} {result : β}
    (success : map <$> computation = .ok result) :
    ∃ value, computation = .ok value ∧ map value = result := by
  cases computation with
  | error error =>
      change Except.error error = Except.ok result at success
      contradiction
  | ok value =>
      refine ⟨value, rfl, ?_⟩
      change Except.ok (map value) = Except.ok result at success
      exact Except.ok.inj success

/-- Repeated fresh-variable allocation makes semantic inference progress,
preserves readiness, and bounds every returned type by the final allocator. -/
theorem freshTypes_inferenceProperties
    (count : Nat) (state : State) (ready : state.InferenceReady) :
    state.InferenceProgress (freshTypes count state).2 ∧
      (freshTypes count state).2.InferenceReady ∧
      ∀ type ∈ (freshTypes count state).1,
        type.VariablesBelow (freshTypes count state).2.inference.next := by
  induction count generalizing state with
  | zero =>
      simp only [freshTypes]
      exact ⟨.refl ready.solved, ready, by simp⟩
  | succ count induction =>
      simp only [freshTypes]
      have freshProgress :=
        State.InferenceProgress.fresh state ready.solved
      have freshReady := State.InferenceReady.fresh ready
      have tailProperties := induction state.fresh.2 freshReady
      have freshTypeBelow :
          state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
        change Ty.VariablesBelow (state.inference.next + 1)
          (.variable ⟨state.inference.next⟩)
        exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
      refine ⟨freshProgress.trans tailProperties.1,
        tailProperties.2.1, ?_⟩
      intro type member
      rcases List.mem_cons.mp member with rfl | member
      · exact freshTypeBelow.weaken tailProperties.1.next_le
      · exact tailProperties.2.2 type member

/-- Successful lambda-parameter binding makes semantic inference progress,
preserves readiness for the extended lexical scope, and bounds every returned
parameter type by the final allocator. -/
theorem bindLambdaParameters_inferenceProperties
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (ready : state.InferenceReady)
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    state.InferenceProgress result.2.2 ∧
      result.2.2.InferenceReady ∧
      ∀ type ∈ result.2.1,
        type.VariablesBelow result.2.2.inference.next := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact ⟨.refl ready.solved, ready, by simp⟩
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind,
            pure, Pure.pure, Except.pure] at success
      | inferred name =>
          by_cases duplicate : name.value ∈ seen
          · simp [bindLambdaParameters, parameterValue, duplicate, bind,
              Except.bind, pure, Pure.pure, Except.pure] at success
          · let type := state.fresh.1
            let freshState := state.fresh.2
            let binderState :=
              (freshState.allocateBinder name.value (.mono type)
                (some parameter.span) false []).2
            cases tailResult : bindLambdaParameters context rest
                (index + 1) (name.value :: seen) binderState with
            | error error =>
                simp [bindLambdaParameters, parameterValue, duplicate,
                  type, freshState, binderState, tailResult, bind,
                  Except.bind, pure, Pure.pure, Except.pure] at success
            | ok tail =>
                rcases tail with ⟨binders, types, finalState⟩
                have resultEq :
                    ((freshState.allocateBinder name.value (.mono type)
                        (some parameter.span) false []).1 :: binders,
                      type :: types, finalState) = result := by
                  simpa [bindLambdaParameters, parameterValue, duplicate,
                    type, freshState, binderState, tailResult, bind,
                    Except.bind, pure, Pure.pure, Except.pure] using success
                subst result
                have freshProgress :
                    state.InferenceProgress freshState := by
                  simpa only [freshState] using
                    State.InferenceProgress.fresh state ready.solved
                have freshReady : freshState.InferenceReady := by
                  simpa only [freshState] using
                    State.InferenceReady.fresh ready
                have freshTypeBelow :
                    type.VariablesBelow freshState.inference.next := by
                  change Ty.VariablesBelow (state.inference.next + 1)
                    (.variable ⟨state.inference.next⟩)
                  exact (Ty.variablesBelow_variable_iff _ _).2
                    (Nat.lt_succ_self _)
                have binderProgress :
                    freshState.InferenceProgress binderState := by
                  simpa only [binderState] using
                    State.InferenceProgress.allocateBinder freshState
                      name.value (.mono type) (some parameter.span) false []
                      freshReady.solved
                have binderReady : binderState.InferenceReady := by
                  simpa only [binderState] using
                    State.InferenceReady.allocateBinder name.value
                      (.mono type) (some parameter.span) false [] freshReady
                      (by
                        simpa only [TypeSystem.Scheme.mono] using
                          freshTypeBelow)
                have tailProperties := induction
                  (index := index + 1) (seen := name.value :: seen)
                  (state := binderState)
                  (result := (binders, types, finalState))
                  binderReady tailResult
                have headBelow :
                    type.VariablesBelow finalState.inference.next :=
                  freshTypeBelow.weaken
                    (Nat.le_trans binderProgress.next_le
                      tailProperties.1.next_le)
                refine ⟨freshProgress.trans
                    (binderProgress.trans tailProperties.1),
                  tailProperties.2.1, ?_⟩
                intro resultType member
                rcases List.mem_cons.mp member with rfl | member
                · exact headBelow
                · exact tailProperties.2.2 resultType member
      | typed marker name sourceType =>
          cases typeResult : resolveSourceType context sourceType with
          | error error =>
              simp [bindLambdaParameters, parameterValue, typeResult, bind,
                Except.bind, pure, Pure.pure, Except.pure] at success
          | ok type =>
              by_cases duplicate : name.value ∈ seen
              · simp [bindLambdaParameters, parameterValue, typeResult,
                  duplicate, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
              · let binderState :=
                  (state.allocateBinder name.value (.mono type)
                    (some parameter.span) marker.isSome []).2
                cases tailResult : bindLambdaParameters context rest
                    (index + 1) (name.value :: seen) binderState with
                | error error =>
                    simp [bindLambdaParameters, parameterValue, typeResult,
                      duplicate, binderState, tailResult, bind, Except.bind,
                      pure, Pure.pure, Except.pure] at success
                | ok tail =>
                    rcases tail with ⟨binders, types, finalState⟩
                    have resultEq :
                        ((state.allocateBinder name.value (.mono type)
                            (some parameter.span) marker.isSome []).1 ::
                          binders,
                          type :: types, finalState) = result := by
                      simpa [bindLambdaParameters, parameterValue, typeResult,
                        duplicate, binderState, tailResult, bind,
                        Except.bind, pure, Pure.pure, Except.pure] using success
                    subst result
                    have typeBelow :
                        type.VariablesBelow state.inference.next :=
                      resolveSourceType_success_variablesBelow typeResult _
                    have binderProgress :
                        state.InferenceProgress binderState := by
                      simpa only [binderState] using
                        State.InferenceProgress.allocateBinder state
                          name.value (.mono type) (some parameter.span)
                          marker.isSome [] ready.solved
                    have binderReady : binderState.InferenceReady := by
                      simpa only [binderState] using
                        State.InferenceReady.allocateBinder name.value
                          (.mono type) (some parameter.span) marker.isSome []
                          ready (by
                            simpa only [TypeSystem.Scheme.mono] using
                              typeBelow)
                    have tailProperties := induction
                      (index := index + 1) (seen := name.value :: seen)
                      (state := binderState)
                      (result := (binders, types, finalState))
                      binderReady tailResult
                    have totalProgress :=
                      binderProgress.trans tailProperties.1
                    have headBelow :
                        type.VariablesBelow finalState.inference.next :=
                      typeBelow.weaken totalProgress.next_le
                    refine ⟨totalProgress, tailProperties.2.1, ?_⟩
                    intro resultType member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact headBelow
                    · exact tailProperties.2.2 resultType member

private def PreservesStateHeader {α : Type} (stateOf : α → State)
    (initial : State) (computation : Except Error α) : Prop :=
  ∀ result, computation = .ok result →
    (stateOf result).header = initial.header

private theorem pair_success_state_header {α : Type}
    {operation : α × State} {value : α} {next initial : State}
    (operationHeader : operation.2.header = initial.header)
    (success : operation = (value, next)) :
    next.header = initial.header := by
  calc
    next.header = operation.2.header := by
      exact (congrArg (fun result => result.2.header) success).symm
    _ = initial.header := operationHeader

private theorem pair_eq_property {α β : Type} {result : α × β}
    {property : β → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {ε α β : Type}
    {computation : Except ε (α × β)} {result : α × β}
    {property : β → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem allocateExpressionId_success_header
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateExpressionId_header state) success

private theorem allocateStatementId_success_header
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateStatementId_header state) success

private theorem state_fresh_success_header
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    next.header = state.header :=
  pair_success_state_header (State.fresh_header state) success

private theorem allocateHiddenLocal_success_header
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateHiddenLocal_header state) success

private theorem addRequirementWithId_success_header
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.addRequirementWithId_header state predicate) success

private theorem addRequirementsWithIds_success_header
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.addRequirementsWithIds_header state predicates) success

private theorem allocateBinder_success_header
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.allocateBinder_header state name scheme span comptime
      schemeRequirements) success

@[simp] private theorem commitCoercionPlan_state_header
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.header = state.header := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      simp

private theorem withExpected_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.header = state.header := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      rfl
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          rfl
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted => simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error => simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none => simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact commitCoercionPlan_state_header state plan

@[simp] private theorem withExpected_preserves_owner
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (withExpected_state_header success)

@[simp] private theorem withExpected_preserves_inputs
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (withExpected_state_header success)

@[simp] private theorem recordExpression_state_header
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State) :
    (recordExpression source expression form requirements coercions state).2.header =
      state.header := by
  exact State.recordNode_header state _

private theorem recordExpressionWithExpected_state_header
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    result.2.header = state.header := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind, except_pure_eq_ok] at success
      subst result
      exact (recordExpression_state_header source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state).trans
          (withExpected_state_header fittedResult)

private theorem bindLambdaParameters_state_header
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    result.2.2.header = state.header := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind,
            Except.pure] at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all [Except.pure]
          all_goals
            subst result
            subst_vars
            have tailHeader := induction _ _ _ (by assumption)
            exact tailHeader.trans (by
              simp_all [State.header, State.fresh, State.allocateBinder])
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error => simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all [Except.pure]
              all_goals
                subst result
                subst_vars
                have tailHeader := induction _ _ _ (by assumption)
                exact tailHeader.trans (by
                  simp_all [State.header, State.allocateBinder])

/-- Successful unification changes only the inference substitution, preserving
the declaration owner and original input binders. -/
@[simp] theorem unify_state_header
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.header = state.header := by
  unfold unify at success
  cases inferenceResult : liftUnification (state.inference.unify left right) with
  | error error => simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      rfl

/-- Successful source-inference unification makes semantic inference progress
when both raw operands lie below the input allocator. -/
theorem unify_inferenceProgress
    {state next : State} {left right : Ty}
    (solved : state.inference.Solved)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (success : unify state left right = .ok next) :
    state.InferenceProgress next := by
  have leftResolvedBelow :
      (state.inference.resolve left).VariablesBelow state.inference.next := by
    simpa [TypeSystem.InferState.resolve] using
      solved.variablesBelow_apply leftBelow
  have rightResolvedBelow :
      (state.inference.resolve right).VariablesBelow state.inference.next := by
    simpa [TypeSystem.InferState.resolve] using
      solved.variablesBelow_apply rightBelow
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      constructor
      · rw [TypeSystem.InferState.unify_next inferenceSuccess]
        exact Nat.le_refl _
      · exact TypeSystem.InferState.Solved.unify solved leftResolvedBelow
          rightResolvedBelow inferenceSuccess
      · exact TypeSystem.InferState.Solved.unify_semanticallyExtends solved
          inferenceSuccess

/-- Successful source-inference unification preserves readiness when both
operands lie below the input allocator. -/
theorem unify_preserves_inferenceReady
    {state next : State} {left right : Ty}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (success : unify state left right = .ok next) :
    next.InferenceReady := by
  have progress := unify_inferenceProgress ready.solved leftBelow rightBelow
    success
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      constructor
      · exact progress.solved
      · change state.binderEnvironment.BodiesBelow inference.next
        exact ready.bindersBelow.weaken progress.next_le

private abbrev finishOperator (context : Context) (dispatch : OperatorDispatch)
    (operand builtin builtinResult resultType : Ty)
    (parameterTypes : List Ty) (hasOpenLiteralOperand : Bool)
    (state : State) : Except Error OperatorInferenceResult :=
  if operand = builtin then
    pure {
      type := builtinResult
      requirements := []
      state
    }
  else
    match dispatch with
    | .function name =>
        if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := resultType
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
        match ← operatorTrait? context traitName with
        | some trait =>
            let predicates ← operatorTraitPredicates context trait methodName
              operand parameterTypes [resultType]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure {
              type := resultType
              requirements
              state
            }
        | none =>
            if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                  builtin operand ||
                isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                  builtin operand then
              pure {
                type := resultType
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishOperator_inferenceProperties
    {context : Context} {dispatch : OperatorDispatch}
    {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {hasOpenLiteralOperand : Bool}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (builtinResultBelow :
      builtinResult.VariablesBelow state.inference.next)
    (resultTypeBelow : resultType.VariablesBelow state.inference.next)
    (success : finishOperator context dispatch operand builtin builtinResult
      resultType parameterTypes hasOpenLiteralOperand state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  unfold finishOperator at success
  by_cases builtinMatch : operand = builtin
  · simp only [builtinMatch, if_true] at success
    injection success with resultEq
    subst result
    exact ⟨.refl ready.solved, ready, builtinResultBelow⟩
  · simp only [builtinMatch, if_false] at success
    cases dispatch with
    | function name =>
        cases deferredResult :
            (isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                builtin operand ||
              isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                builtin operand) with
        | false =>
          simp [deferredResult] at success
        | true =>
          simp only [deferredResult, if_true] at success
          injection success with resultEq
          subst result
          exact ⟨.refl ready.solved, ready, resultTypeBelow⟩
    | traitMethod traitName methodName =>
        cases traitResult : operatorTrait? context traitName with
        | error error =>
            simp [traitResult, bind, Except.bind] at success
        | ok traitOption =>
            cases traitOption with
            | none =>
                simp only [traitResult, bind, Except.bind] at success
                cases deferredResult :
                    (isDeferredBuiltinOperatorTarget state
                        hasOpenLiteralOperand builtin operand ||
                      isStagedIntegerOperatorTarget state
                        hasOpenLiteralOperand builtin operand) with
                | false =>
                  simp [deferredResult] at success
                | true =>
                  simp only [deferredResult, if_true] at success
                  injection success with resultEq
                  subst result
                  exact ⟨.refl ready.solved, ready, resultTypeBelow⟩
            | some trait =>
                simp only [traitResult, bind, Except.bind] at success
                cases predicatesResult : operatorTraitPredicates context trait
                    methodName operand parameterTypes [resultType] with
                | error error =>
                    simp [predicatesResult, bind, Except.bind] at success
                | ok predicates =>
                    simp only [predicatesResult, bind, Except.bind] at success
                    change Except.ok {
                      type := resultType
                      requirements :=
                        (state.addRequirementsWithIds predicates).1
                      state := (state.addRequirementsWithIds predicates).2
                    } = Except.ok result at success
                    injection success with resultEq
                    subst result
                    have progress :=
                      State.InferenceProgress.addRequirementsWithIds state
                        predicates ready.solved
                    have resultReady :=
                      State.InferenceReady.addRequirementsWithIds predicates
                        ready
                    exact ⟨progress, resultReady,
                      resultTypeBelow.weaken progress.next_le⟩

private abbrev finishUnaryOperator (context : Context)
    (operator : Syntax.UnaryOp) (operandType : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve operandType
  let builtin := match operator with
    | .logicalNot => Ty.bool
    | .bitNot => Ty.word
  finishOperator context (unaryOperatorDispatch operator) operand builtin
    builtin (if operator == Syntax.UnaryOp.logicalNot then .bool else operand)
    [operand] hasOpenLiteralOperand state

private theorem finishUnaryOperator_inferenceProperties
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (success : finishUnaryOperator context operator operandType
      hasOpenLiteralOperand state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  have resolvedOperandBelow :
      (state.resolve operandType).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply operandBelow
  have builtinBelow :
      (match operator with
        | .logicalNot => Ty.bool
        | .bitNot => Ty.word).VariablesBelow state.inference.next := by
    cases operator <;>
      exact Ty.variablesBelow_constructor state.inference.next _
  have resultTypeBelow :
      (if operator == Syntax.UnaryOp.logicalNot then .bool
        else state.resolve operandType).VariablesBelow
          state.inference.next := by
    by_cases returnsBool :
        (operator == Syntax.UnaryOp.logicalNot) = true
    · simpa only [returnsBool, if_true, Ty.bool] using
        (Ty.variablesBelow_constructor state.inference.next
          (.builtin .bool))
    · simpa only [returnsBool, Bool.false_eq_true, if_false] using
        resolvedOperandBelow
  exact finishOperator_inferenceProperties ready builtinBelow resultTypeBelow
    (by simpa only [finishUnaryOperator] using success)

private abbrev finishBinaryOperator (context : Context)
    (operator : Syntax.BinaryOp) (left : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve left
  let builtin := binaryBuiltinType operator
  finishOperator context (binaryOperatorDispatch operator) operand builtin
    (if binaryResultIsBool operator then .bool else builtin)
    (if binaryResultIsBool operator then .bool else operand)
    [operand, operand] hasOpenLiteralOperand state

private theorem finishBinaryOperator_inferenceProperties
    {context : Context} {operator : Syntax.BinaryOp} {left : Ty}
    {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (success : finishBinaryOperator context operator left
      hasOpenLiteralOperand state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  have resolvedLeftBelow :
      (state.resolve left).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply leftBelow
  have builtinBelow :
      (if binaryResultIsBool operator then .bool
        else binaryBuiltinType operator).VariablesBelow
          state.inference.next := by
    by_cases returnsBool : binaryResultIsBool operator = true
    · simpa only [returnsBool, if_true, Ty.bool] using
        (Ty.variablesBelow_constructor state.inference.next
          (.builtin .bool))
    · simp only [returnsBool, Bool.false_eq_true, if_false]
      cases operator <;>
        simpa only [binaryBuiltinType, Ty.word, Ty.bool] using
          (Ty.variablesBelow_constructor state.inference.next _)
  have resultTypeBelow :
      (if binaryResultIsBool operator then .bool
        else state.resolve left).VariablesBelow state.inference.next := by
    by_cases returnsBool : binaryResultIsBool operator = true
    · simpa only [returnsBool, if_true, Ty.bool] using
        (Ty.variablesBelow_constructor state.inference.next
          (.builtin .bool))
    · simpa only [returnsBool, Bool.false_eq_true, if_false] using
        resolvedLeftBelow
  exact finishOperator_inferenceProperties ready builtinBelow resultTypeBelow
    (by simpa only [finishBinaryOperator] using success)

/-- Successful unary-operator inference makes semantic inference progress,
preserves readiness, and returns an allocator-bounded result type. -/
theorem inferUnaryOperator_inferenceProperties
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold inferUnaryOperator at success
  cases expected with
  | none =>
      simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at success
      have tailSuccess : finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result := by
        change finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result at success
        exact success
      exact finishUnaryOperator_inferenceProperties ready operandBelow
        tailSuccess
  | some expectedType =>
      have expectedTypeBelow := expectedBelow expectedType (by simp)
      cases skipResult :
          (operator == Syntax.UnaryOp.logicalNot ||
            (state.resolve operandType).freeVariables.isEmpty ||
              !hasOpenLiteralOperand) with
      | true =>
          simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
          have tailSuccess : finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result := by
            change finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result at success
            exact success
          exact finishUnaryOperator_inferenceProperties ready operandBelow
            tailSuccess
      | false =>
          simp only [hasOpenLiteralOperand, skipResult, Bool.false_eq_true,
            if_false] at success
          cases unifyResult : unify state (state.resolve operandType)
              expectedType with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok fittedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have resolvedOperandBelow :
                  (state.resolve operandType).VariablesBelow
                    state.inference.next :=
                ready.solved.variablesBelow_apply operandBelow
              have fitProgress := unify_inferenceProgress ready.solved
                resolvedOperandBelow expectedTypeBelow unifyResult
              have fittedReady := unify_preserves_inferenceReady ready
                resolvedOperandBelow expectedTypeBelow unifyResult
              have operandAtFitted : operandType.VariablesBelow
                  fittedState.inference.next :=
                operandBelow.weaken fitProgress.next_le
              have tailSuccess : finishUnaryOperator context operator
                  operandType hasOpenLiteralOperand fittedState = .ok result := by
                change finishUnaryOperator context operator operandType
                  hasOpenLiteralOperand fittedState = .ok result at success
                exact success
              have tailProperties :=
                finishUnaryOperator_inferenceProperties fittedReady
                  operandAtFitted tailSuccess
              exact ⟨fitProgress.trans tailProperties.1,
                tailProperties.2⟩

/-- Successful binary-operator inference makes semantic inference progress,
preserves readiness, and returns an allocator-bounded result type. -/
theorem inferBinaryOperator_inferenceProperties
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals left ||
      isOpenIntegerLiteralTarget state integerLiterals right
  unfold inferBinaryOperator at success
  cases unifyResult : unify state left right with
  | error error =>
      simp [unifyResult, bind, Except.bind] at success
  | ok unifiedState =>
      simp only [unifyResult, bind, Except.bind] at success
      have unifyProgress := unify_inferenceProgress ready.solved leftBelow
        rightBelow unifyResult
      have unifiedReady := unify_preserves_inferenceReady ready leftBelow
        rightBelow unifyResult
      have leftAtUnified :
          left.VariablesBelow unifiedState.inference.next :=
        leftBelow.weaken unifyProgress.next_le
      cases expected with
      | none =>
          simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
            at success
          have tailSuccess : finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result := by
            change finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result at success
            exact success
          have tailProperties := finishBinaryOperator_inferenceProperties
            unifiedReady leftAtUnified tailSuccess
          exact ⟨unifyProgress.trans tailProperties.1,
            tailProperties.2⟩
      | some expectedType =>
          have expectedTypeBelow : expectedType.VariablesBelow
              unifiedState.inference.next :=
            (expectedBelow expectedType (by simp)).weaken
              unifyProgress.next_le
          cases skipResult :
              (binaryResultIsBool operator ||
                (unifiedState.resolve left).freeVariables.isEmpty ||
                  !hasOpenLiteralOperand) with
          | true =>
              simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
                Except.bind, pure, Pure.pure, Except.pure] at success
              have tailSuccess : finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result := by
                change finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result at success
                exact success
              have tailProperties := finishBinaryOperator_inferenceProperties
                unifiedReady leftAtUnified tailSuccess
              exact ⟨unifyProgress.trans tailProperties.1,
                tailProperties.2⟩
          | false =>
              simp only [hasOpenLiteralOperand, skipResult,
                Bool.false_eq_true, if_false] at success
              have resolvedLeftBelow :
                  (unifiedState.resolve left).VariablesBelow
                    unifiedState.inference.next :=
                unifiedReady.solved.variablesBelow_apply leftAtUnified
              cases fittedResult : unify unifiedState
                  (unifiedState.resolve left) expectedType with
              | error error =>
                  simp [fittedResult, bind, Except.bind] at success
              | ok fittedState =>
                  simp only [fittedResult, bind, Except.bind] at success
                  have fitProgress := unify_inferenceProgress
                    unifiedReady.solved resolvedLeftBelow expectedTypeBelow
                      fittedResult
                  have fittedReady := unify_preserves_inferenceReady
                    unifiedReady resolvedLeftBelow expectedTypeBelow fittedResult
                  have leftAtFitted : left.VariablesBelow
                      fittedState.inference.next :=
                    leftAtUnified.weaken fitProgress.next_le
                  have tailSuccess : finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result := by
                    change finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result at success
                    exact success
                  have tailProperties :=
                    finishBinaryOperator_inferenceProperties fittedReady
                      leftAtFitted tailSuccess
                  exact ⟨unifyProgress.trans
                      (fitProgress.trans tailProperties.1),
                    tailProperties.2⟩

/-- Instantiating a successfully looked-up local binder by advancing only the
inference allocator makes semantic progress, preserves readiness, and leaves
the resolved instantiated body below the new allocator bound. -/
theorem localBinderInstantiation_inferenceProperties
    {state : State} {name : String} {binder : TypedBinder}
    (ready : state.InferenceReady)
    (found : state.lookupBinder? name = some binder) :
    let instantiated :=
      binder.scheme.instantiateWithSubstitution state.inference.next
    let inference := { state.inference with next := instantiated.next }
    let next : State := { state with inference }
    state.InferenceProgress next ∧
      next.InferenceReady ∧
      (next.resolve instantiated.body).VariablesBelow
        next.inference.next := by
  let instantiated :=
    binder.scheme.instantiateWithSubstitution state.inference.next
  let inference := { state.inference with next := instantiated.next }
  let next : State := { state with inference }
  change state.InferenceProgress next ∧
    next.InferenceReady ∧
    (next.resolve instantiated.body).VariablesBelow next.inference.next
  have freeBelow :
      binder.scheme.FreeVariablesBelow state.inference.next :=
    State.InferenceReady.lookupBinder?_freeVariablesBelow ready found
  have nextLe : state.inference.next ≤ next.inference.next := by
    change state.inference.next ≤ instantiated.next
    exact Scheme.instantiateWithSubstitution_next_le
      binder.scheme state.inference.next
  have progress : state.InferenceProgress next :=
    State.InferenceProgress.of_substitution_eq ready.solved nextLe rfl
  have nextReady : next.InferenceReady :=
    State.InferenceReady.of_progress_of_binderEnvironment_eq
      ready progress rfl
  have bodyBelow :
      instantiated.body.VariablesBelow next.inference.next := by
    change instantiated.body.VariablesBelow instantiated.next
    exact Scheme.instantiateWithSubstitution_body_variablesBelow
      binder.scheme state.inference.next freeBelow
  exact ⟨progress, nextReady,
    nextReady.solved.variablesBelow_apply bodyBelow⟩

/-- Expected-type fitting makes semantic inference progress, preserves
readiness, and returns an allocator-bounded expression type. -/
theorem withExpected_inferenceProperties
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : withExpected context state actual expected = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.expression.type.VariablesBelow result.state.inference.next := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      have resolvedBelow :
          (state.resolve actual.type).VariablesBelow state.inference.next :=
        ready.solved.variablesBelow_apply actualBelow
      exact ⟨.refl ready.solved, ready, resolvedBelow⟩
  | some expected =>
      have expectedTypeBelow :
          expected.VariablesBelow state.inference.next :=
        expectedBelow expected (by simp)
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          have actualResolvedBelow :
              (state.inference.resolve actual.type).VariablesBelow
                state.inference.next :=
            ready.solved.variablesBelow_apply actualBelow
          have expectedResolvedBelow :
              (state.inference.resolve expected).VariablesBelow
                state.inference.next :=
            ready.solved.variablesBelow_apply expectedTypeBelow
          have inferenceSolved : inference.Solved :=
            TypeSystem.InferState.Solved.unify ready.solved
              actualResolvedBelow expectedResolvedBelow unification
          have nextEq : inference.next = state.inference.next :=
            TypeSystem.InferState.unify_next unification
          have progress :
              state.InferenceProgress ({ state with inference } : State) := by
            constructor
            · rw [nextEq]
              exact Nat.le_refl _
            · exact inferenceSolved
            · exact TypeSystem.InferState.Solved.unify_semanticallyExtends
                ready.solved unification
          have resultReady :
              ({ state with inference } : State).InferenceReady :=
            State.InferenceReady.of_progress_of_binderEnvironment_eq
              ready progress rfl
          have expectedAtResult :
              expected.VariablesBelow inference.next := by
            rw [nextEq]
            exact expectedTypeBelow
          have resultBelow :
              (({ state with inference } : State).resolve expected).VariablesBelow
                inference.next :=
            inferenceSolved.variablesBelow_apply expectedAtResult
          exact ⟨progress, resultReady, resultBelow⟩
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok planOption =>
                  cases planOption with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      have progress :=
                        commitCoercionPlan_inferenceProgress state plan
                          ready.solved
                      have resultReady :=
                        commitCoercionPlan_preserves_inferenceReady state plan
                          ready
                      have expectedAtResult :
                          expected.VariablesBelow
                            (commitCoercionPlan state plan).2.inference.next :=
                        expectedTypeBelow.weaken progress.next_le
                      have resolvedExpectedBelow :
                          Ty.VariablesBelow
                            (commitCoercionPlan state plan).2.inference.next
                            ((commitCoercionPlan state plan).2.resolve expected) :=
                        resultReady.solved.variablesBelow_apply expectedAtResult
                      refine ⟨progress, resultReady, ?_⟩
                      simpa only [commitCoercionPlan_resolve] using
                        resolvedExpectedBelow

/-- A candidate retained after expected-type fitting inherits its semantic
inference progress, readiness, and allocator-bounded result type. -/
theorem candidateWithExpected_some_inferenceProperties
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.expression.type.VariablesBelow result.state.inference.next := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all [fittedResult]
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_inferenceProperties ready actualBelow expectedBelow
        fittedResult

/-- Successfully recognizing a function type transfers its allocator bound to
both the bundled parameter type and result type. -/
theorem functionParts?_success_variablesBelow
    {type parameter result : Ty} {next : Nat}
    (typeBelow : type.VariablesBelow next)
    (success : functionParts? type = some (parameter, result)) :
    parameter.VariablesBelow next ∧ result.VariablesBelow next := by
  cases type <;>
    simp_all [functionParts?, Ty.variablesBelow_function_iff]

/-- Recovering source parameters from their bundled type preserves allocator
bounds pointwise.  In particular, the arity-one case keeps a product-valued
parameter intact. -/
theorem parameterTypesForArity?_success_variablesBelow
    {arity next : Nat} {parameter : Ty} {parameters : List Ty}
    (parameterBelow : parameter.VariablesBelow next)
    (success : parameterTypesForArity? arity parameter = some parameters) :
    ∀ type ∈ parameters, type.VariablesBelow next := by
  induction arity generalizing parameter parameters with
  | zero =>
      simp only [parameterTypesForArity?] at success
      split at success
      · injection success with parametersEq
        subst parameters
        simp
      · contradiction
  | succ arity induction =>
      cases arity with
      | zero =>
          simp only [parameterTypesForArity?] at success
          injection success with parametersEq
          subst parameters
          intro type member
          have typeEq : type = parameter := by simpa using member
          subst type
          exact parameterBelow
      | succ arity =>
          cases parameter <;>
            simp [parameterTypesForArity?] at success
          case product head rest =>
            have productBelow :=
              (Ty.variablesBelow_product_iff next head rest).mp parameterBelow
            cases tailResult :
                parameterTypesForArity? (arity + 1) rest with
            | none => simp [tailResult] at success
            | some tail =>
                simp [tailResult] at success
                subst parameters
                intro type member
                rcases List.mem_cons.mp member with rfl | member
                · exact productBelow.1
                · exact induction productBelow.2 tailResult type member

/-- Fitting an argument spine makes semantic inference progress and preserves
readiness when every argument and parameter type is allocator-bounded. -/
theorem fitArguments_some_inferenceProperties
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters,
      parameter.VariablesBelow state.inference.next)
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      exact ⟨.refl ready.solved, ready⟩
  | cons argument arguments induction =>
      cases parameters with
      | nil => simp [fitArguments] at success
      | cons parameter parameters =>
          have argumentBelow := argumentsBelow argument (by simp)
          have parameterBelow := parametersBelow parameter (by simp)
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none => simp [fittedResult, bind, Except.bind] at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  have fittedProperties :=
                    candidateWithExpected_some_inferenceProperties ready
                      argumentBelow (by
                        intro expectedType member
                        simp at member
                        subst expectedType
                        exact parameterBelow)
                      fittedResult
                  have tailArgumentsBelow : ∀ tailArgument ∈ arguments,
                      tailArgument.type.VariablesBelow
                        fitted.state.inference.next := by
                    intro tailArgument member
                    exact (argumentsBelow tailArgument (by simp [member])).weaken
                      fittedProperties.1.next_le
                  have tailParametersBelow : ∀ tailParameter ∈ parameters,
                      tailParameter.VariablesBelow
                        fitted.state.inference.next := by
                    intro tailParameter member
                    exact (parametersBelow tailParameter (by simp [member])).weaken
                      fittedProperties.1.next_le
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult, bind, Except.bind] at success
                  | ok tail? =>
                      cases tail? with
                      | none => simp [tailResult, bind, Except.bind] at success
                      | some tail =>
                          simp only [tailResult, bind, Except.bind,
                            except_pure_eq_ok] at success
                          have resultEq : _ = result := Option.some.inj success
                          clear success
                          subst result
                          have tailProperties := induction
                            fittedProperties.2.1 tailArgumentsBelow
                            tailParametersBelow tailResult
                          exact ⟨fittedProperties.1.trans tailProperties.1,
                            tailProperties.2⟩

/-- A retained overload candidate makes semantic inference progress through
declaration instantiation, argument fitting, result fitting, and requirement
allocation.  The final resolved result type remains below the final allocator. -/
theorem tryFunctionCandidate_some_inferenceProperties
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advancedState : State := {
    state with inference := {
      state.inference with next := instantiated.next
    }
  }
  have instantiatedNextLe :
      state.inference.next ≤ instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_next_le signature.scheme
        state.inference.next
  have advanceProgress : state.InferenceProgress advancedState := by
    refine State.InferenceProgress.of_substitution_eq ready.solved ?_ ?_
    · simpa only [advancedState] using instantiatedNextLe
    · rfl
  have advancedReady : advancedState.InferenceReady :=
    State.InferenceReady.of_progress_of_binderEnvironment_eq ready
      advanceProgress rfl
  have instantiatedBodyBelow :
      instantiated.body.VariablesBelow instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_body_variablesBelow
        signature.scheme state.inference.next schemeBodyBelow
  have argumentsAtAdvanced : ∀ argument ∈ arguments,
      argument.type.VariablesBelow advancedState.inference.next := by
    intro argument member
    exact (argumentsBelow argument member).weaken advanceProgress.next_le
  unfold tryFunctionCandidate at success
  dsimp only at success
  cases partsResult : functionParts?
      (signature.scheme.instantiate state.inference.next).body with
  | none =>
      rw [partsResult] at success
      simp at success
  | some parts =>
      rcases parts with ⟨parameterType, resultType⟩
      rw [partsResult] at success
      have localPartsResult :
          functionParts? instantiated.body =
            some (parameterType, resultType) := by
        simpa only [instantiated] using partsResult
      have partsBelow := functionParts?_success_variablesBelow
        instantiatedBodyBelow localPartsResult
      cases parametersResult : parameterTypesForArity?
          signature.parameterTypes.length parameterType with
      | none => simp [parametersResult] at success
      | some parameterTypes =>
          simp only [parametersResult] at success
          have parameterTypesBelowAtInstantiation :=
            parameterTypesForArity?_success_variablesBelow partsBelow.1
              parametersResult
          have parameterTypesBelow : ∀ parameter ∈ parameterTypes,
              parameter.VariablesBelow advancedState.inference.next := by
            simpa only [advancedState] using
              parameterTypesBelowAtInstantiation
          cases argumentsResult : fitArguments context advancedState arguments
              parameterTypes with
          | error error =>
              simp [instantiated, advancedState, argumentsResult, bind,
                Except.bind] at success
          | ok fittedArguments? =>
              cases fittedArguments? with
              | none =>
                  simp [instantiated, advancedState, argumentsResult, bind,
                    Except.bind] at success
              | some fittedArguments =>
                  simp only [instantiated, advancedState, argumentsResult, bind,
                    Except.bind] at success
                  have fittedArgumentsProperties :=
                    fitArguments_some_inferenceProperties advancedReady
                      argumentsAtAdvanced parameterTypesBelow argumentsResult
                  have resultTypeAtAdvanced :
                      resultType.VariablesBelow
                        advancedState.inference.next := by
                    simpa only [advancedState] using partsBelow.2
                  have resultTypeAtArguments :
                      resultType.VariablesBelow
                        fittedArguments.state.inference.next :=
                    resultTypeAtAdvanced.weaken
                      fittedArgumentsProperties.1.next_le
                  have expectedAtArguments : ∀ expectedType ∈ expected,
                      expectedType.VariablesBelow
                        fittedArguments.state.inference.next := by
                    intro expectedType member
                    exact (expectedBelow expectedType member).weaken
                      (Nat.le_trans advanceProgress.next_le
                        fittedArgumentsProperties.1.next_le)
                  cases fittedResultResult : candidateWithExpected context
                      fittedArguments.state { id := call, type := resultType }
                      expected with
                  | error error =>
                      simp [fittedResultResult, bind, Except.bind] at success
                  | ok fittedResult? =>
                      cases fittedResult? with
                      | none =>
                          simp [fittedResultResult, bind, Except.bind] at success
                      | some fittedResult =>
                          simp only [fittedResultResult, bind, Except.bind]
                            at success
                          have fittedResultProperties :=
                            candidateWithExpected_some_inferenceProperties
                              fittedArgumentsProperties.2 resultTypeAtArguments
                              expectedAtArguments fittedResultResult
                          cases integerValidation :
                              validateCandidateIntegerLiterals context
                                fittedResult.state integerLiteralOrigins with
                          | error error =>
                              simp [integerValidation, bind, Except.bind] at success
                          | ok hasDeferredIntegerLiterals =>
                              simp only [integerValidation, bind, Except.bind]
                                at success
                              cases predicateValidation :
                                  validateCandidatePredicates context
                                    fittedResult.state
                                    (instantiated.predicates ++
                                      fittedResult.state.requirements.map
                                        (fun requirement =>
                                          requirement.predicate)) with
                              | error error =>
                                  have expandedPredicateValidation :
                                      validateCandidatePredicates context
                                          fittedResult.state
                                          ((signature.scheme.instantiate
                                                state.inference.next).predicates ++
                                            fittedResult.state.requirements.map
                                              (fun requirement =>
                                                requirement.predicate)) =
                                        .error error := by
                                    simpa only [instantiated] using
                                      predicateValidation
                                  rw [expandedPredicateValidation] at success
                                  simp at success
                              | ok validated =>
                                  cases validated
                                  have expandedPredicateValidation :
                                      validateCandidatePredicates context
                                          fittedResult.state
                                          ((signature.scheme.instantiate
                                                state.inference.next).predicates ++
                                            fittedResult.state.requirements.map
                                              (fun requirement =>
                                                requirement.predicate)) =
                                        .ok () := by
                                    simpa only [instantiated] using
                                      predicateValidation
                                  rw [expandedPredicateValidation] at success
                                  simp at success
                                  let allocation :=
                                    fittedResult.state.addRequirementsWithIds
                                      instantiated.predicates
                                  let finalState :=
                                    allocation.2.markDirectCallRequirements
                                      allocation.1
                                  have requirementsProgress :
                                      fittedResult.state.InferenceProgress
                                        allocation.2 :=
                                    State.InferenceProgress.addRequirementsWithIds
                                      fittedResult.state instantiated.predicates
                                      fittedResultProperties.2.1.solved
                                  have requirementsReady :
                                      allocation.2.InferenceReady :=
                                    State.InferenceReady.addRequirementsWithIds
                                      instantiated.predicates
                                      fittedResultProperties.2.1
                                  have directProgress :
                                      allocation.2.InferenceProgress finalState :=
                                    State.InferenceProgress.markDirectCallRequirements
                                      allocation.2
                                      allocation.1 requirementsReady.solved
                                  have finalReady : finalState.InferenceReady :=
                                    State.InferenceReady.markDirectCallRequirements
                                      allocation.1
                                      requirementsReady
                                  have fittedTypeAtFinal :
                                      fittedResult.expression.type.VariablesBelow
                                        finalState.inference.next :=
                                    fittedResultProperties.2.2.weaken
                                      (Nat.le_trans requirementsProgress.next_le
                                        directProgress.next_le)
                                  have resolvedTypeBelow :
                                      (finalState.resolve
                                        fittedResult.expression.type).VariablesBelow
                                          finalState.inference.next :=
                                    finalReady.solved.variablesBelow_apply
                                      fittedTypeAtFinal
                                  have resultEq : ({
                                      instantiation :=
                                        DeclarationInstantiation.ofInstantiated
                                          signature instantiated
                                      result := {
                                        fittedResult.expression with
                                        type := finalState.resolve
                                          fittedResult.expression.type
                                      }
                                      argumentCoercions :=
                                        fittedArguments.coercions
                                      callCoercions := fittedResult.coercions
                                      signatureRequirements := allocation.1
                                      hasDeferredIntegerLiterals
                                      state := finalState
                                      cost := fittedArguments.cost +
                                        fittedResult.coercions.length
                                    } : CandidateAttemptResult) = result := by
                                    simpa only [instantiated, allocation,
                                      finalState,
                                      ConstrainedDeclarationScheme.instantiate_predicates]
                                      using success
                                  subst result
                                  exact ⟨advanceProgress.trans
                                      (fittedArgumentsProperties.1.trans
                                        (fittedResultProperties.1.trans
                                          (requirementsProgress.trans
                                            directProgress))),
                                    finalReady, resolvedTypeBelow⟩

/-- Attaching delayed argument-coercion metadata leaves semantic inference
unchanged and preserves the stable-binder readiness invariant. -/
theorem attachExpressionCoercions_inferenceProperties
    (state : State) (entries : List ExpressionCoercions)
    (ready : state.InferenceReady) :
    state.InferenceProgress (attachExpressionCoercions state entries) ∧
      (attachExpressionCoercions state entries).InferenceReady := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil =>
      exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      let modify : ExpressionNode → ExpressionNode := fun node => {
        node with
        type := entry.coercions.foldl (fun _ step => step.target) node.type
        requirements := node.requirements ++
          coercionRequirements entry.coercions
        coercions := node.coercions ++ entry.coercions
      }
      let modifiedState :=
        state.modifyExpressionNode entry.expression modify
      have modifiedProgress : state.InferenceProgress modifiedState := by
        exact State.InferenceProgress.modifyExpressionNode state
          entry.expression modify ready.solved
      have modifiedReady : modifiedState.InferenceReady := by
        exact State.InferenceReady.modifyExpressionNode entry.expression modify
          ready
      have tailProperties := induction modifiedState modifiedReady
      exact ⟨modifiedProgress.trans tailProperties.1, tailProperties.2⟩

/-- Recording the synthetic callee and selected call changes only typed-source
metadata.  It therefore makes reflexive semantic inference progress, preserves
readiness, and retains the caller-supplied bound for the returned expression. -/
theorem recordSelectedCallResult_inferenceProperties
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State)
    (ready : state.InferenceReady)
    (resultBelow : result.type.VariablesBelow state.inference.next) :
    state.InferenceProgress
        (recordSelectedCallResult source callee name arguments attempt result
          trailingCoercions state).2 ∧
      (recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).2.InferenceReady ∧
      (recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).1.type.VariablesBelow
        (recordSelectedCallResult source callee name arguments attempt result
          trailingCoercions state).2.inference.next := by
  let attachedState :=
    attachExpressionCoercions state attempt.argumentCoercions
  have attachedProperties :
      state.InferenceProgress attachedState ∧ attachedState.InferenceReady :=
    attachExpressionCoercions_inferenceProperties state
      attempt.argumentCoercions ready
  let allocation := attachedState.allocateExpressionId
  have allocatedProgress :
      attachedState.InferenceProgress allocation.2 :=
    State.InferenceProgress.allocateExpressionId attachedState
      attachedProperties.2.solved
  have allocatedReady : allocation.2.InferenceReady :=
    State.InferenceReady.allocateExpressionId attachedProperties.2
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  have calleeProgress :
      allocation.2.InferenceProgress calleeRecord.2 := by
    simpa only [calleeRecord, recordExpression] using
      State.InferenceProgress.recordNode allocation.2 (.expression {
        id := calleeExpression.id
        span := callee.span
        type := calleeExpression.type
        form := .reference name (.declaration attempt.instantiation)
        requirements := []
        coercions := []
      }) allocatedReady.solved
  have calleeReady : calleeRecord.2.InferenceReady := by
    simpa only [calleeRecord, recordExpression] using
      State.InferenceReady.recordNode (.expression {
        id := calleeExpression.id
        span := callee.span
        type := calleeExpression.type
        form := .reference name (.declaration attempt.instantiation)
        requirements := []
        coercions := []
      }) allocatedReady
  let callRecord := recordExpression source result
    (.call allocation.1 (arguments.map (fun argument => argument.id))
      (.declaration attempt.instantiation))
    (coercionRequirements attempt.callCoercions ++
      attempt.signatureRequirements ++
      coercionRequirements trailingCoercions)
    (attempt.callCoercions ++ trailingCoercions) calleeRecord.2
  have callProgress : calleeRecord.2.InferenceProgress callRecord.2 := by
    simpa only [callRecord, recordExpression] using
      State.InferenceProgress.recordNode calleeRecord.2 (.expression {
        id := result.id
        span := source.span
        type := result.type
        form := .call allocation.1
          (arguments.map (fun argument => argument.id))
          (.declaration attempt.instantiation)
        requirements := coercionRequirements attempt.callCoercions ++
          attempt.signatureRequirements ++
          coercionRequirements trailingCoercions
        coercions := attempt.callCoercions ++ trailingCoercions
      }) calleeReady.solved
  have callReady : callRecord.2.InferenceReady := by
    simpa only [callRecord, recordExpression] using
      State.InferenceReady.recordNode (.expression {
        id := result.id
        span := source.span
        type := result.type
        form := .call allocation.1
          (arguments.map (fun argument => argument.id))
          (.declaration attempt.instantiation)
        requirements := coercionRequirements attempt.callCoercions ++
          attempt.signatureRequirements ++
          coercionRequirements trailingCoercions
        coercions := attempt.callCoercions ++ trailingCoercions
      }) calleeReady
  have totalProgress : state.InferenceProgress callRecord.2 :=
    attachedProperties.1.trans
      (allocatedProgress.trans (calleeProgress.trans callProgress))
  have returnedBelow :
      callRecord.1.type.VariablesBelow callRecord.2.inference.next := by
    simpa only [callRecord, recordExpression] using
      resultBelow.weaken totalProgress.next_le
  change state.InferenceProgress callRecord.2 ∧
    callRecord.2.InferenceReady ∧
    callRecord.1.type.VariablesBelow callRecord.2.inference.next
  exact ⟨totalProgress, callReady, returnedBelow⟩

/-- The ordinary selected-call wrapper inherits the inference guarantees of
the general result-recording operation. -/
theorem recordSelectedCall_inferenceProperties
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (ready : attempt.state.InferenceReady)
    (resultBelow : attempt.result.type.VariablesBelow
      attempt.state.inference.next) :
    attempt.state.InferenceProgress
        (recordSelectedCall source callee name arguments attempt).2 ∧
      (recordSelectedCall source callee name arguments attempt).2.InferenceReady ∧
      (recordSelectedCall source callee name arguments attempt).1.type.VariablesBelow
        (recordSelectedCall source callee name arguments attempt).2.inference.next := by
  simpa only [recordSelectedCall] using
    recordSelectedCallResult_inferenceProperties source callee name arguments
      attempt attempt.result [] attempt.state ready resultBelow

/-- Expected-type fitting followed by expression recording has the same
inference guarantees; recording the typed node leaves inference unchanged. -/
theorem recordExpressionWithExpected_inferenceProperties
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (typeBelow : type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  obtain ⟨fitted, fittedSuccess, resultExpression, resultState⟩ :=
    recordExpressionWithExpected_success_record success
  have fittedProperties := withExpected_inferenceProperties ready typeBelow
    expectedBelow fittedSuccess
  rw [resultExpression, resultState]
  have recordedProgress :=
    State.InferenceProgress.recordNode fitted.state (.expression {
      id := fitted.expression.id
      span := source.span
      type := fitted.expression.type
      form
      requirements := requirements ++
        coercionRequirements fitted.coercions
      coercions := fitted.coercions
    }) fittedProperties.2.1.solved
  have recordedReady :=
    State.InferenceReady.recordNode (.expression {
      id := fitted.expression.id
      span := source.span
      type := fitted.expression.type
      form
      requirements := requirements ++
        coercionRequirements fitted.coercions
      coercions := fitted.coercions
    }) fittedProperties.2.1
  exact ⟨fittedProperties.1.trans recordedProgress, recordedReady,
    fittedProperties.2.2⟩

/-- Instantiating one top-level function reference, allocating its predicate
requirements, and recording the reference makes semantic inference progress,
preserves readiness, and returns an allocator-bounded expression type. -/
theorem recordInstantiatedFunctionReference_inferenceProperties
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {name : String} {signature : ProgramFunctionSignature}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (schemeBodyBelow : signature.scheme.body.VariablesBelow
      state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success :
      (let instantiated :=
          signature.scheme.instantiate state.inference.next
       let inference := {
         state.inference with next := instantiated.next
       }
       let (requirements, state) :=
         ({ state with inference }).addRequirementsWithIds
           instantiated.predicates
       recordExpressionWithExpected context source id instantiated.body
         (.reference name (.declaration
           (DeclarationInstantiation.ofInstantiated signature instantiated)))
         requirements expected state) = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advancedState : State := {
    state with inference := {
      state.inference with next := instantiated.next
    }
  }
  let allocation :=
    advancedState.addRequirementsWithIds instantiated.predicates
  have instantiatedNextLe :
      state.inference.next ≤ instantiated.next := by
    simpa only [instantiated] using
      ConstrainedDeclarationScheme.instantiate_next_le signature.scheme
        state.inference.next
  have advanceProgress : state.InferenceProgress advancedState := by
    refine State.InferenceProgress.of_substitution_eq ready.solved ?_ ?_
    · simpa only [advancedState] using instantiatedNextLe
    · rfl
  have advancedReady : advancedState.InferenceReady :=
    State.InferenceReady.of_progress_of_binderEnvironment_eq ready
      advanceProgress rfl
  have instantiatedBelow :
      instantiated.body.VariablesBelow advancedState.inference.next := by
    simpa only [instantiated, advancedState] using
      ConstrainedDeclarationScheme.instantiate_body_variablesBelow
        signature.scheme state.inference.next schemeBodyBelow
  have requirementsProgress :
      advancedState.InferenceProgress allocation.2 :=
    State.InferenceProgress.addRequirementsWithIds advancedState
      instantiated.predicates advancedReady.solved
  have requirementsReady : allocation.2.InferenceReady := by
    exact State.InferenceReady.addRequirementsWithIds
      instantiated.predicates advancedReady
  have bodyAtRequirements :
      instantiated.body.VariablesBelow allocation.2.inference.next :=
    instantiatedBelow.weaken requirementsProgress.next_le
  have expectedAtRequirements : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocation.2.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (Nat.le_trans advanceProgress.next_le requirementsProgress.next_le)
  have recordSuccess :
      recordExpressionWithExpected context source id instantiated.body
        (.reference name (.declaration
          (DeclarationInstantiation.ofInstantiated signature instantiated)))
        allocation.1 expected allocation.2 = .ok result := by
    simpa only [instantiated, advancedState, allocation, Prod.eta] using success
  have recordedProperties :=
    recordExpressionWithExpected_inferenceProperties requirementsReady
      bodyAtRequirements expectedAtRequirements recordSuccess
  exact ⟨advanceProgress.trans
      (requirementsProgress.trans recordedProperties.1),
    recordedProperties.2.1, recordedProperties.2.2⟩

/-- Successful source-inference unification makes the original input types
equal under the returned inference state. -/
theorem unify_resolve_eq
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.inference.resolve left = next.inference.resolve right := by
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      exact TypeSystem.InferState.unify_resolve_eq inferenceSuccess

/-- Any type equality already visible through the input inference state
remains visible after a successful incremental unification. -/
theorem unify_preserves_resolve_eq
    {state next : State} {left right first second : Ty}
    (equal : state.resolve first = state.resolve second)
    (success : unify state left right = .ok next) :
    next.resolve first = next.resolve second := by
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      unfold State.resolve at equal ⊢
      unfold TypeSystem.InferState.unify at inferenceSuccess
      cases updateSuccess : TypeSystem.Unification.unifyTypes
          (state.inference.resolve left) (state.inference.resolve right) with
      | error error =>
          simp [updateSuccess, bind, Except.bind] at inferenceSuccess
      | ok update =>
          simp [updateSuccess, bind, Except.bind] at inferenceSuccess
          cases inferenceSuccess
          simpa [TypeSystem.InferState.resolve,
            TypeSystem.Substitution.compose_apply] using
              congrArg update.apply equal

@[simp] private theorem unify_preserves_owner
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.owner = state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (unify_state_header success)

@[simp] private theorem unify_preserves_inputs
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.inputs = state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (unify_state_header success)

private theorem freshDataConstructorInstantiation_fold_inferenceProperties
    (parameters : List TypeParameterId) (arguments : List Ty) (state : State)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.VariablesBelow state.inference.next) :
    let result := parameters.foldl
      (fun (result : List Ty × State) _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2))
      (arguments, state)
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      ∀ argument ∈ result.1,
        argument.VariablesBelow result.2.inference.next := by
  induction parameters generalizing arguments state with
  | nil =>
      simp only [List.foldl_nil]
      exact ⟨State.InferenceProgress.refl ready.solved, ready,
        argumentsBelow⟩
  | cons parameter parameters induction =>
      simp only [List.foldl_cons]
      let allocation := state.fresh
      have allocationProgress : state.InferenceProgress allocation.2 := by
        simpa only [allocation] using
          State.InferenceProgress.fresh state ready.solved
      have allocationReady : allocation.2.InferenceReady := by
        simpa only [allocation] using State.InferenceReady.fresh ready
      have freshTypeBelow :
          allocation.1.VariablesBelow allocation.2.inference.next := by
        have below :
            state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
          change Ty.VariablesBelow (state.inference.next + 1)
            (.variable ⟨state.inference.next⟩)
          exact (Ty.variablesBelow_variable_iff _ _).2
            (Nat.lt_succ_self _)
        simpa only [allocation] using below
      have extendedArgumentsBelow :
          ∀ argument ∈ arguments ++ [allocation.1],
            argument.VariablesBelow allocation.2.inference.next := by
        intro argument member
        rcases List.mem_append.mp member with member | member
        · exact (argumentsBelow argument member).weaken
            allocationProgress.next_le
        · simp only [List.mem_singleton] at member
          subst argument
          exact freshTypeBelow
      have tailProperties := induction (arguments ++ [allocation.1])
        allocation.2 allocationReady extendedArgumentsBelow
      exact ⟨allocationProgress.trans tailProperties.1,
        tailProperties.2.1, tailProperties.2.2⟩

/-- Freshly instantiating a data constructor advances semantic inference,
preserves readiness, and bounds every generated replacement and instantiated
constructor type at the returned allocator. -/
theorem freshDataConstructorInstantiation_inferenceProperties
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State)
    (ready : state.InferenceReady)
    (payloadTypesBelow : ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow state.inference.next) :
    let result := freshDataConstructorInstantiation dataType constructor state
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      (∀ parameter replacement,
        (parameter, replacement) ∈ result.1.parameterSubstitution →
          replacement.VariablesBelow result.2.inference.next) ∧
      (∀ payload ∈ result.1.payloadTypes,
        payload.VariablesBelow result.2.inference.next) ∧
      result.1.resultType.VariablesBelow result.2.inference.next := by
  let allocation := dataType.parameters.foldl
    (fun (result : List Ty × State) _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2))
    ([], state)
  have allocationProperties :
      state.InferenceProgress allocation.2 ∧
        allocation.2.InferenceReady ∧
        ∀ argument ∈ allocation.1,
          argument.VariablesBelow allocation.2.inference.next := by
    simpa only [allocation] using
      freshDataConstructorInstantiation_fold_inferenceProperties
        dataType.parameters [] state ready (by simp)
  change state.InferenceProgress allocation.2 ∧
    allocation.2.InferenceReady ∧
    (∀ parameter replacement,
      (parameter, replacement) ∈ dataType.parameters.zip allocation.1 →
        replacement.VariablesBelow allocation.2.inference.next) ∧
    (∀ payload ∈ constructor.payloadTypes.map
      (ParameterSubstitution.apply
        (dataType.parameters.zip allocation.1)),
      payload.VariablesBelow allocation.2.inference.next) ∧
    (Ty.nominal dataType.id allocation.1).VariablesBelow
      allocation.2.inference.next
  have rangeBelow : ∀ parameter replacement,
      (parameter, replacement) ∈ dataType.parameters.zip allocation.1 →
        replacement.VariablesBelow allocation.2.inference.next := by
    intro parameter replacement member
    exact allocationProperties.2.2 replacement (List.of_mem_zip member).2
  have instantiatedPayloadsBelow : ∀ payload ∈
      constructor.payloadTypes.map
        (ParameterSubstitution.apply
          (dataType.parameters.zip allocation.1)),
      payload.VariablesBelow allocation.2.inference.next := by
    intro payload member
    rcases List.mem_map.mp member with
      ⟨sourcePayload, sourceMember, rfl⟩
    apply ParameterSubstitution.apply_variables_below
    · intro parameter replacement entryMember
      exact rangeBelow parameter replacement entryMember
    · exact (payloadTypesBelow sourcePayload sourceMember).weaken
        allocationProperties.1.next_le
  exact ⟨allocationProperties.1, allocationProperties.2.1, rangeBelow,
    instantiatedPayloadsBelow,
    Ty.variablesBelow_nominal allocationProperties.2.2⟩

@[simp] private theorem freshTypes_preserves_header
    (count : Nat) (state : State) :
    (freshTypes count state).2.header = state.header := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [freshTypes]
      rw [induction]
      exact State.fresh_header state

@[simp] private theorem freshTypes_preserves_owner
    (count : Nat) (state : State) :
    (freshTypes count state).2.owner = state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (freshTypes_preserves_header count state)

@[simp] private theorem freshTypes_preserves_inputs
    (count : Nat) (state : State) :
    (freshTypes count state).2.inputs = state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (freshTypes_preserves_header count state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_header
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.header =
      state.header := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldHeader (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.header =
        accumulator.2.header := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        rw [induction]
        exact State.fresh_header accumulator.2
  unfold freshDataConstructorInstantiation
  exact foldHeader dataType.parameters ([], state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_owner
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.owner =
      state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (freshDataConstructorInstantiation_preserves_header dataType constructor
      state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_inputs
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.inputs =
      state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (freshDataConstructorInstantiation_preserves_header dataType constructor
      state)

private theorem inferMatchPatternFlatFuel_preserves_header
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesStateHeader InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        PreservesStateHeader InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        PreservesStateHeader InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesStateHeader at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have headerEq := unify_state_header (by assumption)
    all_goals try have ownerEq := unify_preserves_owner (by assumption)
    all_goals try have inputsEq := unify_preserves_inputs (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try simp_all [State.header, State.fresh,
      State.addRequirementWithId, State.allocateBinder, bind, Except.bind]
    all_goals grind [unify_preserves_owner, unify_preserves_inputs,
      freshDataConstructorInstantiation_preserves_owner,
      freshDataConstructorInstantiation_preserves_inputs,
      freshTypes_preserves_owner, freshTypes_preserves_inputs]

/-- Successful pattern inference preserves the declaration-scoped state
header. -/
theorem inferMatchPatternFuel_state_header
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    result.2.header = state.header := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact inferMatchPatternFlatFuel_preserves_header fuel context pattern
        expected [] state inferred flatResult

private theorem inferUnaryOperator_state_header
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem inferBinaryOperator_state_header
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem candidateWithExpected_some_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.header = state.header := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all [fittedResult]
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_state_header fittedResult

private theorem fitArguments_some_state_header
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.header = state.header := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      rfl
  | cons argument arguments induction =>
      cases parameters with
      | nil => simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none => simp [fittedResult, bind, Except.bind] at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult, bind, Except.bind] at success
                  | ok tail? =>
                      cases tail? with
                      | none => simp [tailResult, bind, Except.bind] at success
                      | some tail =>
                          simp only [tailResult, bind, Except.bind,
                            except_pure_eq_ok] at success
                          have resultEq : _ = result := Option.some.inj success
                          clear success
                          subst result
                          exact (induction tailResult).trans
                            (candidateWithExpected_some_state_header fittedResult)

/-- A successful function-candidate attempt retains exactly the generic
instantiation allocated before argument fitting, expected-type fitting, and
predicate validation.  None of those later checks may replace the selected
declaration or its shared parameter substitution. -/
theorem tryFunctionCandidate_some_instantiation
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.instantiation =
      DeclarationInstantiation.ofInstantiated signature
        (signature.scheme.instantiate state.inference.next) := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals simp_all

private theorem tryFunctionCandidate_some_state_header
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.header = state.header := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fitHeader :=
    fitArguments_some_state_header (by assumption)
  all_goals try have expectedHeader :=
    candidateWithExpected_some_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId, State.markDirectCallRequirements]

private theorem collectCandidateAttempts_success_header
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {state : State}
    (attemptHeader : ∀ signature result,
      attempt signature = .ok (some result) →
        result.state.header = state.header) :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        success.attempt.state.header = state.header := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro success member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction success member
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction success member
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl successEq =>
                  subst success
                  exact attemptHeader signature result attemptResult
              | inr member => exact induction success member

private theorem collectCandidateAttempts_success_provenance
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)} :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        ∃ signature, signature ∈ candidates ∧
          attempt signature = .ok (some success.attempt) := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro success member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
            induction success member
          exact ⟨selected, by simp [selectedMember], selectedSuccess⟩
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
                induction success member
              exact ⟨selected, by simp [selectedMember], selectedSuccess⟩
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl successEq =>
                  subst success
                  exact ⟨signature, by simp, attemptResult⟩
              | inr member =>
                  obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
                    induction success member
                  exact ⟨selected, by simp [selectedMember], selectedSuccess⟩

private theorem bestCandidateSuccesses_subset
    (successes : List CandidateSuccess) :
    bestCandidateSuccesses successes ⊆ successes := by
  intro success member
  unfold bestCandidateSuccesses at member
  dsimp only at member
  split at member
  · contradiction
  · have preferredMember := (List.mem_filter.mp member).1
    by_cases empty :
        (successes.filter fun success =>
          !success.attempt.hasDeferredIntegerLiterals).isEmpty
    · simpa [empty] using preferredMember
    · have groundMember :
          success ∈ successes.filter fun success =>
            !success.attempt.hasDeferredIntegerLiterals := by
        simpa [empty] using preferredMember
      exact (List.mem_filter.mp groundMember).1

/-- Every successfully selected overload is the unchanged successful result
of checking one signature from the caller-provided candidate list.  Ranking
may discard other successes, but it cannot synthesize or rewrite the retained
candidate attempt. -/
theorem selectFunctionCandidateFrom_success_candidate
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∃ signature, signature ∈ candidates ∧
      tryFunctionCandidate context arguments integerLiteralOrigins call
        expected state signature = .ok (some result) := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_subset search.successes
                (by simp [selected])
            simpa [attempt] using
              (collectCandidateAttempts_success_provenance
                candidates candidate member)

/-- Selecting an overload preserves the inference guarantees established for
the retained candidate attempt. -/
theorem selectFunctionCandidateFrom_inferenceProperties
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (candidateBodiesBelow : ∀ signature ∈ candidates,
      signature.scheme.body.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  obtain ⟨signature, signatureMember, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_some_inferenceProperties ready argumentsBelow
    (candidateBodiesBelow signature signatureMember) expectedBelow
    candidateSuccess

/-- Overload ranking returns one unchanged successful candidate attempt, so
its requirement ledger is canonical whenever the shared input ledger is. -/
theorem selectFunctionCandidateFrom_preserves_requirementsWellFormed
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_preserves_requirementsWellFormed
    candidateSuccess wellFormed

/-- Resolving the visible overload set is state-free; successful ordinary
selection therefore inherits the explicit-candidate ledger guarantee. -/
theorem selectFunctionCandidate_preserves_requirementsWellFormed
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_preserves_requirementsWellFormed
        success wellFormed

private theorem selectFunctionCandidateFrom_state_header
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.header = state.header := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_subset search.successes
                (by simp [selected])
            exact collectCandidateAttempts_success_header
              (state := state)
              (fun signature result attemptSuccess =>
                tryFunctionCandidate_some_state_header attemptSuccess)
              candidates candidate member

@[simp] private theorem attachExpressionCoercions_state_header
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).header = state.header := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction _).trans
        (State.modifyExpressionNode_header state entry.expression _)

@[simp] private theorem recordSelectedCall_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.header =
      attempt.state.header := by
  simp [recordSelectedCall, recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.header = state.header := by
  simp [recordSelectedCallResult]

/-- Applying an indirectly obtained function type makes semantic inference
progress, preserves readiness, and returns an allocator-bounded result type. -/
theorem applyFunctionType_inferenceProperties
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (ready : state.InferenceReady)
    (calleeBelow : calleeType.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.result.type.VariablesBelow result.state.inference.next := by
  have argumentTypesBelow :
      ∀ type ∈ arguments.map (fun argument => argument.type),
        type.VariablesBelow state.inference.next := by
    intro type member
    simp only [List.mem_map] at member
    obtain ⟨argument, argumentMember, rfl⟩ := member
    exact argumentsBelow argument argumentMember
  have argumentTypeBelow :
      (Ty.productMany
        (arguments.map (fun argument => argument.type))).VariablesBelow
          state.inference.next :=
    Ty.variablesBelow_productMany argumentTypesBelow
  have resolvedCalleeBelow :
      (state.resolve calleeType).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply calleeBelow
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      have partsBelow := functionParts?_success_variablesBelow
        resolvedCalleeBelow partsResult
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany
              (arguments.map (fun argument => argument.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          have argumentProperties := withExpected_inferenceProperties ready
            argumentTypeBelow (by
              intro expectedType member
              simp at member
              subst expectedType
              exact partsBelow.1)
            argumentResult
          have returnTypeBelow :
              returnType.VariablesBelow
                fittedArgument.state.inference.next :=
            partsBelow.2.weaken argumentProperties.1.next_le
          have expectedAtArgument : ∀ expectedType ∈ expected,
              expectedType.VariablesBelow
                fittedArgument.state.inference.next := by
            intro expectedType member
            exact (expectedBelow expectedType member).weaken
              argumentProperties.1.next_le
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have resultProperties := withExpected_inferenceProperties
                argumentProperties.2.1 returnTypeBelow expectedAtArgument
                resultResult
              exact ⟨argumentProperties.1.trans resultProperties.1,
                resultProperties.2⟩
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      have freshProgress : state.InferenceProgress freshState := by
        have progress := State.InferenceProgress.fresh state ready.solved
        rw [freshResultEq] at progress
        exact progress
      have freshReady : freshState.InferenceReady := by
        have nextReady := State.InferenceReady.fresh ready
        rw [freshResultEq] at nextReady
        exact nextReady
      have freshTypeBelow :
          state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
        change Ty.VariablesBelow (state.inference.next + 1)
          (.variable ⟨state.inference.next⟩)
        exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
      rw [freshResultEq] at freshTypeBelow
      have calleeAtFresh :
          calleeType.VariablesBelow freshState.inference.next :=
        calleeBelow.weaken freshProgress.next_le
      have argumentTypeAtFresh :
          (Ty.productMany
            (arguments.map (fun argument => argument.type))).VariablesBelow
              freshState.inference.next :=
        argumentTypeBelow.weaken freshProgress.next_le
      have functionTypeBelow :
          (Ty.function
            (Ty.productMany (arguments.map (fun argument => argument.type)))
            resultType).VariablesBelow freshState.inference.next :=
        (Ty.variablesBelow_function_iff _ _ _).2
          ⟨argumentTypeAtFresh, freshTypeBelow⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun argument =>
            argument.type)) resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          have unifyProgress := unify_inferenceProgress freshReady.solved
            calleeAtFresh functionTypeBelow unifyResult
          have unifiedReady := unify_preserves_inferenceReady freshReady
            calleeAtFresh functionTypeBelow unifyResult
          have prefixProgress := freshProgress.trans unifyProgress
          have resultTypeAtUnified :
              resultType.VariablesBelow unifiedState.inference.next :=
            freshTypeBelow.weaken unifyProgress.next_le
          have expectedAtUnified : ∀ expectedType ∈ expected,
              expectedType.VariablesBelow unifiedState.inference.next := by
            intro expectedType member
            exact (expectedBelow expectedType member).weaken
              prefixProgress.next_le
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have resultProperties := withExpected_inferenceProperties
                unifiedReady resultTypeAtUnified expectedAtUnified resultResult
              exact ⟨prefixProgress.trans resultProperties.1,
                resultProperties.2⟩

private theorem applyFunctionType_state_header
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.header = state.header := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact (withExpected_state_header resultResult).trans
                (withExpected_state_header argumentResult)
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact (withExpected_state_header resultResult).trans
                ((unify_state_header unifyResult).trans
                  (state_fresh_success_header freshResultEq))

@[simp] private theorem recordIndirectCall_state_header
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.header =
      result.state.header := by
  simp [recordIndirectCall]

private theorem unifyBuiltinFunctionArgumentsEqual_state_header
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.header = state.header := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      rfl
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          rfl
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unifiedState =>
              simp only [unifyResult, bind, Except.bind] at success
              exact (induction success).trans (unify_state_header unifyResult)

private theorem recordBuiltinFunctionCall_state_header
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.header = state.header := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentsHeader :=
    unifyBuiltinFunctionArgumentsEqual_state_header (by assumption)
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.header, State.allocateExpressionId,
    State.recordNode, recordExpression, bind, Except.bind]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem syntheticTuple_result_state_header
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    result.snd.header = state.header := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [except_pure_eq_ok] using success
  rw [← resultEq]
  simp only [State.recordNode_header, State.allocateExpressionId_header]

private theorem pure_pair_result_state_header {ε α : Type}
    {value : α} {next initial : State} {
      result : α × State}
    (nextHeader : next.header = initial.header)
    (success : (pure (value, next) : Except ε (α × State)) = .ok result) :
    result.snd.header = initial.header := by
  have resultEq : (value, next) = result := by
    simpa only [except_pure_eq_ok] using success
  rw [← resultEq]
  exact nextHeader

private theorem pair_result_state_header {α : Type}
    {value : α} {next initial : State} {result : α × State}
    (nextHeader : next.header = initial.header)
    (success : (value, next) = result) :
    result.snd.header = initial.header := by
  rw [← success]
  exact nextHeader

private theorem restore_state_header {state initial : State}
    {scope : LexicalScope} (header : state.header = initial.header) :
    (state.restoreLexicalScope scope).header = initial.header :=
  (State.restoreLexicalScope_header state scope).trans header

private theorem restored_pair_result_state_header {α : Type}
    {value : α} {state initial : State} {scope : LexicalScope}
    {result : α × State}
    (header : state.header = initial.header)
    (success : (value, state.restoreLexicalScope scope) = result) :
    result.snd.header = initial.header :=
  pair_result_state_header (restore_state_header header) success

set_option maxHeartbeats 500000 in
private theorem inferStatementsFuel_preserves_header_internal
    (fuel : Nat) (context : Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) :
    PreservesStateHeader BlockResult.state state
      (inferStatementsFuel fuel context statements expectedReturn state) := by
  apply inferStatementsFuel.induct
    (motive1 := fun fuel context expression expected state =>
      PreservesStateHeader Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesStateHeader Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesStateHeader Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesStateHeader BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesStateHeader StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesStateHeader InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesStateHeader Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesStateHeader Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesStateHeader (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesStateHeader Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesStateHeader MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesStateHeader at *
    intro result success
    have statementIdHeader :=
      allocateStatementId_success_header statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsHeader :=
      expressionsInduction _ (by assumption)
    all_goals try have casesHeader :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodyHeader :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleHeader :=
      syntheticTuple_result_state_header (by assumption)
    all_goals try have defaultHeader :=
      pure_pair_result_state_header casesHeader (by assumption)
    all_goals simp_all only [Prod.eta, except_pure_eq_ok,
      State.allocateExpressionId_header, State.allocateHiddenLocal_header,
      State.restoreLexicalScope_header, State.recordNode_header]
    all_goals try exact
      restored_pair_result_state_header bodyHeader (by assumption)
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesStateHeader at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have placeHeader :=
      pair_except_property placeInduction (by assumption)
    all_goals try have valueHeader :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedHeader := unify_state_header (by assumption)
    all_goals simp_all [Prod.eta]
  case case67 =>
    unfold PreservesStateHeader at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesStateHeader at *
    intro result success
    first
      | unfold inferExprFuel at success
      | unfold inferConstructorApplicationFuel at success
      | unfold inferConstructorArgumentsFuel at success
      | unfold inferStatementsFuel at success
      | unfold inferStatementFuel at success
      | unfold inferForItemsFuel at success
      | unfold inferForItemFuel at success
      | unfold inferPlaceFuel at success
      | unfold inferAssignedValueFuel at success
      | unfold inferExprsFuel at success
      | unfold inferMatchCasesFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | have ih1Header := pair_eq_property ih1
      | have ih1Header := pair_except_property ih1 (by assumption)
      | have ih1Header := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Header := pair_eq_property ih2
      | have ih2Header := pair_except_property ih2 (by assumption)
      | have ih2Header := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Header := pair_eq_property ih3
      | have ih3Header := pair_except_property ih3 (by assumption)
      | have ih3Header := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have headerEq := unify_state_header (by assumption)
    all_goals try have expressionIdHeader :=
      allocateExpressionId_success_header (by assumption)
    all_goals try have statementIdHeader :=
      allocateStatementId_success_header (by assumption)
    all_goals try have freshHeader := state_fresh_success_header (by assumption)
    all_goals try have hiddenLocalHeader :=
      allocateHiddenLocal_success_header (by assumption)
    all_goals try have requirementHeader :=
      addRequirementWithId_success_header (by assumption)
    all_goals try have requirementsHeader :=
      addRequirementsWithIds_success_header (by assumption)
    all_goals try have binderHeader :=
      allocateBinder_success_header (by assumption)
    all_goals try have recordHeader :=
      recordExpressionWithExpected_state_header (by assumption)
    all_goals try have lambdaHeader :=
      bindLambdaParameters_state_header (by assumption)
    all_goals try have patternHeader :=
      inferMatchPatternFuel_state_header (by assumption)
    all_goals try have unaryHeader :=
      inferUnaryOperator_state_header (by assumption)
    all_goals try have binaryHeader :=
      inferBinaryOperator_state_header (by assumption)
    all_goals try have selectionHeader :=
      selectFunctionCandidateFrom_state_header (by assumption)
    all_goals try have expectedHeader :=
      withExpected_state_header (by assumption)
    all_goals try have applicationHeader :=
      applyFunctionType_state_header (by assumption)
    all_goals try have builtinHeader :=
      recordBuiltinFunctionCall_state_header (by assumption)
    all_goals try simp_all
    all_goals try simp_all [State.header, State.fresh,
      State.addRequirementWithId, State.addRequirementsWithIds,
      State.allocateBinder, State.allocateHiddenLocal,
      State.restoreLexicalScope, State.recordNode, bind, Except.bind]
    all_goals grind [unify_preserves_owner, unify_preserves_inputs,
      freshDataConstructorInstantiation_preserves_owner,
      freshDataConstructorInstantiation_preserves_inputs,
      freshTypes_preserves_owner, freshTypes_preserves_inputs]

/-- Successful statement-list inference preserves the declaration owner and
the original input binders. -/
theorem inferStatementsFuel_state_header
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.header = state.header := by
  exact inferStatementsFuel_preserves_header_internal fuel context statements
    expectedReturn state result success

@[simp] theorem inferStatementsFuel_preserves_owner
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferStatementsFuel_state_header success)

@[simp] theorem inferStatementsFuel_preserves_inputs
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferStatementsFuel_state_header success)

end Solcore.Frontend.SourceInference.Detail
