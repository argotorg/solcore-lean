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

/-- Invert the successful local-identifier branch through its canonical scheme
instantiation and requirement allocation, stopping at the exact expression
recording operation used by the traversal. -/
theorem inferExprFuel_success_localIdentifier_record
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {result : InferredExpression × State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : inferExprFuel (fuel + 1) context expression expected initial =
      .ok result) :
    (let instantiationStart := allocated.inference.next
     let instantiated :=
       binder.scheme.instantiateWithSubstitution instantiationStart
     let inference := {
       allocated.inference with next := instantiated.next
     }
     let advanced : State := { allocated with inference }
     let predicates := binder.schemeRequirements.map fun requirement =>
       applyPredicate advanced
         (TypedTraitResolution.applySubstitution instantiated.substitution
           requirement.predicate)
     let (requirements, recorded) :=
       advanced.addRequirementsWithIds predicates
     recordExpressionWithExpected context expression id
       (advanced.resolve instantiated.body)
       (.reference name.value (.local binder.id)) requirements expected recorded
       (localSchemeInstantiationStart := some instantiationStart) = .ok result) := by
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, lookupEq] at success
  simpa only using success

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

@[simp] private theorem addRequirementsWithIds_inference
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference =
      state.inference := by
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

/-- A successful concrete expected-type fit remains equal to that expectation
under every substitution which semantically extends the returned inference
substitution.  This direct inversion covers both ordinary unification and a
committed coercion plan. -/
private theorem withExpected_some_apply_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Ty} {result : ExpectationResult} {outer : Substitution}
    (success : withExpected context state actual (some expected) = .ok result)
    (extension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    outer.apply result.expression.type = outer.apply expected := by
  cases unification : state.inference.unify actual.type expected with
  | ok inference =>
      simp only [withExpected, unification] at success
      injection success with resultEq
      subst result
      exact extension expected
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
                  change outer.apply (state.resolve expected) =
                    outer.apply expected
                  rw [← commitCoercionPlan_resolve state plan expected]
                  exact extension expected

/-- Expected-type fitting followed by node recording retains the same
semantic equality; recording changes source metadata but not inference. -/
private theorem recordExpressionWithExpected_some_apply_eq
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State} {outer : Substitution}
    (success : recordExpressionWithExpected context source id type form
      requirements (some expected) state localSchemeInstantiationStart =
        .ok result)
    (extension : outer.SemanticallyExtends
      result.2.inference.substitution) :
    outer.apply result.1.type = outer.apply expected := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type }
      (some expected) with
  | error error =>
      simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok _ = Except.ok result at success
      injection success with resultEq
      subst result
      apply withExpected_some_apply_eq fittedResult
      simpa only [recordExpression, State.recordNode] using extension

/-- Retaining an expected-type candidate does not weaken the semantic
equality established by the underlying successful fit. -/
private theorem candidateWithExpected_some_apply_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Ty} {result : ExpectationResult} {outer : Substitution}
    (success : candidateWithExpected context state actual (some expected) =
      .ok (some result))
    (extension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    outer.apply result.expression.type = outer.apply expected := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual (some expected) with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all [fittedResult]
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_some_apply_eq fittedResult extension

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

/-- Recursive inference may allocate declaration-local identities, but never
moves the shared allocator cutoff backwards. -/
private def AdvancesNextLocal {α : Type} (stateOf : α → State)
    (initial : State) (computation : Except Error α) : Prop :=
  ∀ result, computation = .ok result →
    initial.nextLocal ≤ (stateOf result).nextLocal

private def PreservesLexicalScope {α : Type} (stateOf : α → State)
    (initial : State) (computation : Except Error α) : Prop :=
  ∀ result, computation = .ok result →
    (stateOf result).lexicalScope = initial.lexicalScope

private def RestoresOuterScope {α : Type} (stateOf : α → State)
    (outerScope : LexicalScope) (initial : State)
    (computation : Except Error α) : Prop :=
  ∀ result, computation = .ok result →
    initial.lexicalScope = outerScope →
      (stateOf result).lexicalScope = outerScope

private theorem pair_success_state_header {α : Type}
    {operation : α × State} {value : α} {next initial : State}
    (operationHeader : operation.2.header = initial.header)
    (success : operation = (value, next)) :
    next.header = initial.header := by
  calc
    next.header = operation.2.header := by
      exact (congrArg (fun result => result.2.header) success).symm
    _ = initial.header := operationHeader

private theorem pair_success_lexicalScope {α : Type}
    {operation : α × State} {value : α} {next initial : State}
    (operationScope : operation.2.lexicalScope = initial.lexicalScope)
    (success : operation = (value, next)) :
    next.lexicalScope = initial.lexicalScope := by
  calc
    next.lexicalScope = operation.2.lexicalScope := by
      exact (congrArg (fun result => result.2.lexicalScope) success).symm
    _ = initial.lexicalScope := operationScope

private theorem pair_success_nextLocal {α : Type}
    {operation : α × State} {value : α} {next initial : State}
    (operationNext : operation.2.nextLocal = initial.nextLocal)
    (success : operation = (value, next)) :
    next.nextLocal = initial.nextLocal := by
  calc
    next.nextLocal = operation.2.nextLocal := by
      exact (congrArg (fun result => result.2.nextLocal) success).symm
    _ = initial.nextLocal := operationNext

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

private theorem allocateExpressionId_success_lexicalScope
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    next.lexicalScope = state.lexicalScope :=
  pair_success_lexicalScope rfl success

private theorem allocateExpressionId_success_nextLocal
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    next.nextLocal = state.nextLocal :=
  pair_success_nextLocal rfl success

private theorem allocateStatementId_success_header
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateStatementId_header state) success

private theorem allocateStatementId_success_lexicalScope
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.lexicalScope = state.lexicalScope :=
  pair_success_lexicalScope rfl success

private theorem allocateStatementId_success_nextLocal
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.nextLocal = state.nextLocal :=
  pair_success_nextLocal rfl success

private theorem state_fresh_success_header
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    next.header = state.header :=
  pair_success_state_header (State.fresh_header state) success

private theorem state_fresh_success_lexicalScope
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    next.lexicalScope = state.lexicalScope :=
  pair_success_lexicalScope rfl success

private theorem state_fresh_success_nextLocal
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    next.nextLocal = state.nextLocal :=
  pair_success_nextLocal rfl success

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

@[simp] private theorem addRequirementsWithIds_lexicalScope
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.lexicalScope =
      state.lexicalScope := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

@[simp] private theorem addRequirementsWithIds_nextLocal
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.nextLocal =
      state.nextLocal := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

@[simp] private theorem addRequirementsWithIds_locals
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.locals = state.locals := by
  exact congrArg LexicalScope.locals
    (addRequirementsWithIds_lexicalScope state predicates)

@[simp] private theorem addRequirementsWithIds_localBinders
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.localBinders =
      state.localBinders := by
  exact congrArg LexicalScope.binders
    (addRequirementsWithIds_lexicalScope state predicates)

private theorem addRequirementsWithIds_success_lexicalScope
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates =
      (requirements, next)) :
    next.lexicalScope = state.lexicalScope := by
  calc
    next.lexicalScope = (requirements, next).2.lexicalScope := rfl
    _ = (state.addRequirementsWithIds predicates).2.lexicalScope :=
      congrArg (fun pair => pair.2.lexicalScope) success.symm
    _ = state.lexicalScope := addRequirementsWithIds_lexicalScope state predicates

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

@[simp] private theorem commitCoercionPlan_lexicalScope
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.lexicalScope = state.lexicalScope := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      rw [addRequirementsWithIds_lexicalScope]
      rfl

@[simp] private theorem commitCoercionPlan_nextLocal
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.nextLocal = state.nextLocal := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      rw [addRequirementsWithIds_nextLocal]
      rfl

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

private theorem withExpected_lexicalScope
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.lexicalScope = state.lexicalScope := by
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
                      exact commitCoercionPlan_lexicalScope state plan

private theorem withExpected_nextLocal
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.nextLocal = state.nextLocal := by
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
                      exact commitCoercionPlan_nextLocal state plan

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
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.header =
      state.header := by
  exact State.recordNode_header state _

@[simp] private theorem recordNode_lexicalScope
    (state : State) (node : Node) :
    (state.recordNode node).lexicalScope = state.lexicalScope := by
  rfl

@[simp] private theorem recordNode_nextLocal (state : State) (node : Node) :
    (state.recordNode node).nextLocal = state.nextLocal := by
  rfl

@[simp] private theorem recordNode_locals (state : State) (node : Node) :
    (state.recordNode node).locals = state.locals := by
  rfl

@[simp] private theorem recordNode_localBinders (state : State) (node : Node) :
    (state.recordNode node).localBinders = state.localBinders := by
  rfl

@[simp] private theorem recordExpression_lexicalScope
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.lexicalScope =
      state.lexicalScope := by
  rfl

@[simp] private theorem recordExpression_nextLocal
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.nextLocal = state.nextLocal := by
  rfl

private theorem recordExpressionWithExpected_state_header
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.header = state.header := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind, except_pure_eq_ok] at success
      subst result
      exact (recordExpression_state_header source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state
        (localSchemeInstantiationStart := localSchemeInstantiationStart)).trans
          (withExpected_state_header fittedResult)

private theorem recordExpressionWithExpected_lexicalScope
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.lexicalScope = state.lexicalScope := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind, except_pure_eq_ok] at success
      subst result
      exact withExpected_lexicalScope fittedResult

private theorem recordExpressionWithExpected_nextLocal
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.nextLocal = state.nextLocal := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind, except_pure_eq_ok] at success
      subst result
      exact withExpected_nextLocal fittedResult

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

/-- Parameter binding extends a transient lambda scope without moving the
shared declaration-local allocator backwards. -/
private theorem bindLambdaParameters_nextLocal_le
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    state.nextLocal ≤ result.2.2.nextLocal := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact Nat.le_refl _
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
            have tailNext := induction _ _ _ (by assumption)
            simp_all [State.fresh, State.allocateBinder]
            omega
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
                have tailNext := induction _ _ _ (by assumption)
                simp_all [State.allocateBinder]
                omega

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

@[simp] private theorem unify_preserves_lexicalScope
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.lexicalScope = state.lexicalScope := by
  unfold unify at success
  cases inferenceResult : liftUnification (state.inference.unify left right) with
  | error error => simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      rfl

@[simp] private theorem unify_preserves_nextLocal
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.nextLocal = state.nextLocal := by
  unfold unify at success
  cases inferenceResult : liftUnification (state.inference.unify left right) with
  | error error => simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      rfl

@[simp] private theorem unify_preserves_locals
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.locals = state.locals :=
  congrArg LexicalScope.locals (unify_preserves_lexicalScope success)

@[simp] private theorem unify_preserves_localBinders
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.localBinders = state.localBinders :=
  congrArg LexicalScope.binders (unify_preserves_lexicalScope success)

theorem unify_preserves_localBindersBelowNextLocal
    {state next : State} {left right : Ty}
    (below : state.LocalBindersBelowNextLocal)
    (success : unify state left right = .ok next) :
    next.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
      (unify_preserves_localBinders success) ?_ below
  rw [unify_preserves_nextLocal success]
  exact Nat.le_refl _

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
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (typeBelow : type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
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
      localSchemeInstantiationStart
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
      localSchemeInstantiationStart
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

/-- A successful contextual-constructor lookup supplies allocator-bounded
type arguments, so formation validation bounds every instantiated payload and
the constructor result at the input state's allocator. -/
theorem contextualConstructorCandidate_success_instantiation_variablesBelow
    {context : Context} {state : State} {expected : Option Ty}
    {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (success : contextualConstructorCandidate context state expected name =
      .ok (dataType, constructor, arguments)) :
    (∀ payload ∈
        (instantiateDataConstructor dataType constructor arguments).payloadTypes,
      payload.VariablesBelow state.inference.next) ∧
      Ty.VariablesBelow state.inference.next
        (instantiateDataConstructor dataType constructor arguments).resultType := by
  rcases contextualConstructorCandidate_success_facts success with
    ⟨dataMember, constructorMember, expectedType, expectedEq, nominalEq⟩
  have expectedTypeBelow :
      expectedType.VariablesBelow state.inference.next :=
    expectedBelow expectedType (by simp [expectedEq])
  have resolvedExpectedBelow :
      (state.resolve expectedType).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedTypeBelow
  rw [nominalEq] at resolvedExpectedBelow
  have argumentsBelow : ∀ argument ∈ arguments,
      argument.VariablesBelow state.inference.next :=
    ((Ty.variablesBelow_applyMany_iff state.inference.next
      (.constructor (.declaration dataType.id)) arguments).mp (by
        simpa only [Ty.nominal] using resolvedExpectedBelow)).2
  have payloadTypesBelow : ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow state.inference.next :=
    validated.data_constructor_payloadTypes_variablesBelow dataMember
      constructorMember state.inference.next
  exact instantiateDataConstructor_types_variablesBelow argumentsBelow
    payloadTypesBelow

private theorem freshDataConstructorInstantiation_fold_length
    (parameters : List TypeParameterId) (arguments : List Ty) (state : State) :
    let result := parameters.foldl
      (fun (result : List Ty × State) _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2))
      (arguments, state)
    result.1.length = arguments.length + parameters.length := by
  induction parameters generalizing arguments state with
  | nil => simp
  | cons parameter parameters induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp
      omega

private theorem freshDataConstructorInstantiation_fold_range_is_variable
    (parameters : List TypeParameterId) (arguments : List Ty) (state : State)
    (arguments_are_variables : ∀ argument ∈ arguments,
      ∃ metavariable, argument = Ty.variable metavariable) :
    let result := parameters.foldl
      (fun (result : List Ty × State) _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2))
      (arguments, state)
    ∀ argument ∈ result.1,
      ∃ metavariable, argument = Ty.variable metavariable := by
  induction parameters generalizing arguments state with
  | nil => simpa using arguments_are_variables
  | cons parameter parameters induction =>
      simp only [List.foldl_cons]
      apply induction
      intro argument member
      rcases List.mem_append.mp member with old | fresh
      · exact arguments_are_variables argument old
      · simp only [List.mem_singleton] at fresh
        subst argument
        exact ⟨⟨state.inference.next⟩, rfl⟩

/-- Successful constructor freshening exposes the source-ordered row of fresh
flexible arguments used by the canonical constructor instantiation. -/
theorem freshDataConstructorInstantiation_success_shape
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    ∃ arguments,
      arguments.length = dataType.parameters.length ∧
        (∀ argument ∈ arguments,
          ∃ metavariable, argument = Ty.variable metavariable) ∧
        instantiation =
          instantiateDataConstructor dataType constructor arguments := by
  let allocation := dataType.parameters.foldl
    (fun (result : List Ty × State) _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2))
    ([], state)
  have allocation_length :
      allocation.1.length = dataType.parameters.length := by
    simpa only [allocation, List.length_nil, Nat.zero_add] using
      freshDataConstructorInstantiation_fold_length dataType.parameters [] state
  have allocation_range : ∀ argument ∈ allocation.1,
      ∃ metavariable, argument = Ty.variable metavariable := by
    simpa only [allocation] using
      freshDataConstructorInstantiation_fold_range_is_variable
        dataType.parameters [] state (by simp)
  have instantiation_eq := congrArg Prod.fst success
  change instantiateDataConstructor dataType constructor allocation.1 =
    instantiation at instantiation_eq
  exact ⟨allocation.1, allocation_length, allocation_range,
    instantiation_eq.symm⟩

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

@[simp] private theorem freshTypes_preserves_nextLocal
    (count : Nat) (state : State) :
    (freshTypes count state).2.nextLocal = state.nextLocal := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [freshTypes]
      rw [induction]
      rfl

theorem freshTypes_preserves_localBindersBelowNextLocal
    (count : Nat) (state : State)
    (below : state.LocalBindersBelowNextLocal) :
    (freshTypes count state).2.LocalBindersBelowNextLocal := by
  induction count generalizing state with
  | zero => exact below
  | succ count induction =>
      simp only [freshTypes]
      exact induction state.fresh.2
        (State.fresh_preserves_localBindersBelowNextLocal state below)

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

@[simp] theorem freshDataConstructorInstantiation_preserves_lexicalScope
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.lexicalScope =
      state.lexicalScope := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldScope (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.lexicalScope =
        accumulator.2.lexicalScope := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        rw [induction]
        rfl
  unfold freshDataConstructorInstantiation
  exact foldScope dataType.parameters ([], state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_nextLocal
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.nextLocal =
      state.nextLocal := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldNextLocal (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.nextLocal =
        accumulator.2.nextLocal := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        rw [induction]
        rfl
  unfold freshDataConstructorInstantiation
  exact foldNextLocal dataType.parameters ([], state)

theorem
    freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State)
    (below : state.LocalBindersBelowNextLocal) :
    (freshDataConstructorInstantiation dataType constructor state).2
      |>.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
  · exact congrArg LexicalScope.binders
      (freshDataConstructorInstantiation_preserves_lexicalScope
        dataType constructor state)
  · rw [freshDataConstructorInstantiation_preserves_nextLocal]
    exact Nat.le_refl _
  · exact below

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

private def MatchPatternFlatInferenceProperties (context : Context)
    (_pattern : Syntax.Pattern) (expected : Ty) (_seen : List String)
    (state : State) (computation : Except Error InferredPattern) : Prop :=
  ∀ result,
    state.InferenceReady →
    expected.VariablesBelow state.inference.next →
    ProgramSignatureFormationValidated context.signatures →
    computation = .ok result →
    state.InferenceProgress result.state ∧ result.state.InferenceReady

private def MatchPatternsFlatInferenceProperties (context : Context)
    (_patterns : List Syntax.Pattern) (expectedTypes : List Ty)
    (_seen : List String) (state : State)
    (computation : Except Error InferredPatterns) : Prop :=
  ∀ result,
    state.InferenceReady →
    (∀ expected ∈ expectedTypes,
      expected.VariablesBelow state.inference.next) →
    ProgramSignatureFormationValidated context.signatures →
    computation = .ok result →
    state.InferenceProgress result.state ∧ result.state.InferenceReady

/-- Contextual constructor selection followed by result-type unification
advances inference monotonically, preserves readiness, and bounds every
instantiated payload type at the returned allocator. -/
theorem contextualConstructorPrefix_inferenceProperties
    {context : Context} {state next : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (selected : contextualConstructorCandidate context state (some expected)
      name = .ok (dataType, constructor, arguments))
    (unified : unify state
      (instantiateDataConstructor dataType constructor arguments).resultType
      expected = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady ∧
      ∀ payload ∈
        (instantiateDataConstructor dataType constructor arguments).payloadTypes,
        payload.VariablesBelow next.inference.next := by
  have bounded :=
    contextualConstructorCandidate_success_instantiation_variablesBelow
      ready (by
        intro retained member
        simp only [Option.mem_def] at member
        cases Option.some.inj member
        exact expectedBelow) validated selected
  have progress := unify_inferenceProgress ready.solved bounded.2
    expectedBelow unified
  have nextReady := unify_preserves_inferenceReady ready bounded.2
    expectedBelow unified
  exact ⟨progress, nextReady, fun payload member =>
    (bounded.1 payload member).weaken progress.next_le⟩

/-- Explicit constructor selection, fresh generic instantiation, and
result-type unification advance inference monotonically, preserve readiness,
and bound every instantiated payload type at the returned allocator. -/
theorem explicitConstructorPrefix_inferenceProperties
    {context : Context} {state allocated next : State} {expected : Ty}
    {qualifiers : List String} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (selected : explicitConstructorCandidate context qualifiers name =
      .ok (dataType, constructor))
    (freshEq : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, allocated))
    (unified : unify allocated instantiation.resultType expected = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady ∧
      ∀ payload ∈ instantiation.payloadTypes,
        payload.VariablesBelow next.inference.next := by
  rcases explicitConstructorCandidate_success_members selected with
    ⟨dataMember, constructorMember⟩
  have rawBelow :=
    validated.data_constructor_payloadTypes_variablesBelow dataMember
      constructorMember state.inference.next
  have allocatedProperties :=
    freshDataConstructorInstantiation_inferenceProperties dataType constructor
      state ready rawBelow
  simp only [freshEq] at allocatedProperties
  have expectedBelowAllocated :=
    expectedBelow.weaken allocatedProperties.1.next_le
  have progress := unify_inferenceProgress allocatedProperties.2.1.solved
    allocatedProperties.2.2.2.2 expectedBelowAllocated unified
  have nextReady := unify_preserves_inferenceReady allocatedProperties.2.1
    allocatedProperties.2.2.2.2 expectedBelowAllocated unified
  exact ⟨allocatedProperties.1.trans progress, nextReady,
    fun payload member =>
      (allocatedProperties.2.2.2.1 payload member).weaken progress.next_le⟩

private theorem tuplePatternPrefix_inferenceProperties
    {state allocated next : State} {expected : Ty} {count : Nat}
    {elementTypes : List Ty}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (freshEq : freshTypes count state = (elementTypes, allocated))
    (unified : unify allocated expected (Ty.productMany elementTypes) =
      .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady ∧
      ∀ element ∈ elementTypes,
        element.VariablesBelow next.inference.next := by
  have allocatedProperties := freshTypes_inferenceProperties count state ready
  simp only [freshEq] at allocatedProperties
  have expectedBelowAllocated :=
    expectedBelow.weaken allocatedProperties.1.next_le
  have productBelow :=
    Ty.variablesBelow_productMany allocatedProperties.2.2
  have progress := unify_inferenceProgress allocatedProperties.2.1.solved
    expectedBelowAllocated productBelow unified
  have nextReady := unify_preserves_inferenceReady allocatedProperties.2.1
    expectedBelowAllocated productBelow unified
  exact ⟨allocatedProperties.1.trans progress, nextReady,
    fun element member =>
      (allocatedProperties.2.2 element member).weaken progress.next_le⟩

private theorem integerPatternPrefix_inferenceProperties
    {state recorded next : State} {expected : Ty}
    {metavariable : TypeVarId} {normalized : Ty}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (freshTypeEq : state.fresh.1 = .variable metavariable)
    (unified : unify recorded (.variable metavariable) normalized = .ok next)
    (normalizedEq : recorded.resolve expected = normalized)
    (recordedInferenceEq : recorded.inference =
      (state.fresh.2.addRequirementWithId
        (ProgramSignatures.builtinIntPredicate
          (.variable metavariable))).2.inference)
    (recordedBinderEnvironmentEq : recorded.binderEnvironment =
      (state.fresh.2.addRequirementWithId
        (ProgramSignatures.builtinIntPredicate
          (.variable metavariable))).2.binderEnvironment) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  let required := state.fresh.2.addRequirementWithId
    (ProgramSignatures.builtinIntPredicate (.variable metavariable))
  have freshProgress := State.InferenceProgress.fresh state ready.solved
  have freshReady := State.InferenceReady.fresh ready
  have requirementProgress :
      state.fresh.2.InferenceProgress required.2 := by
    simpa only [required] using State.InferenceProgress.addRequirementWithId
      state.fresh.2
      (ProgramSignatures.builtinIntPredicate (.variable metavariable))
      freshReady.solved
  have requirementReady : required.2.InferenceReady := by
    simpa only [required] using State.InferenceReady.addRequirementWithId
      (ProgramSignatures.builtinIntPredicate (.variable metavariable))
      freshReady
  have recordProgress : required.2.InferenceProgress recorded := by
    apply State.InferenceProgress.of_inference_eq requirementReady.solved
    simpa only [required] using recordedInferenceEq
  have recordReady : recorded.InferenceReady := by
    apply State.InferenceReady.of_progress_of_binderEnvironment_eq
      requirementReady recordProgress
    simpa only [required] using recordedBinderEnvironmentEq
  have prefixProgress :=
    freshProgress.trans (requirementProgress.trans recordProgress)
  have freshTargetBelow :
      state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
    change Ty.VariablesBelow (state.inference.next + 1)
      (.variable ⟨state.inference.next⟩)
    exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
  have targetBelow :
      (Ty.variable metavariable).VariablesBelow recorded.inference.next := by
    rw [← freshTypeEq]
    exact freshTargetBelow.weaken
      (Nat.le_trans requirementProgress.next_le recordProgress.next_le)
  have expectedResolvedBelow :
      normalized.VariablesBelow recorded.inference.next := by
    rw [← normalizedEq]
    exact prefixProgress.resolve_variablesBelow expectedBelow
  have unifiedProgress := unify_inferenceProgress recordReady.solved
    targetBelow expectedResolvedBelow unified
  have unifiedReady := unify_preserves_inferenceReady recordReady targetBelow
    expectedResolvedBelow unified
  exact ⟨prefixProgress.trans unifiedProgress, unifiedReady⟩

private theorem binderPattern_inferenceProperties
    {state : State} {expected : Ty} {name : String}
    {span : Syntax.SourceSpan}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next) :
    state.InferenceProgress
        (state.allocateBinder name (.mono (state.resolve expected))
          (some span)).2 ∧
      (state.allocateBinder name (.mono (state.resolve expected))
        (some span)).2.InferenceReady := by
  have resolvedExpectedBelow :
      (state.resolve expected).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedBelow
  exact ⟨State.InferenceProgress.allocateBinder state name
      (.mono (state.resolve expected)) (some span) false [] ready.solved,
    State.InferenceReady.allocateBinder name (.mono (state.resolve expected))
      (some span) false [] ready resolvedExpectedBelow⟩

set_option maxHeartbeats 500000 in
private theorem inferMatchPatternFlatFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    MatchPatternFlatInferenceProperties context pattern expected seen state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        MatchPatternFlatInferenceProperties context pattern expected seen state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expectedTypes seen state =>
        MatchPatternsFlatInferenceProperties context patterns expectedTypes seen
          state (inferMatchPatternsFlatFuel fuel context patterns expectedTypes
            seen state))
  case case3 =>
    intros
    unfold MatchPatternFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      exact integerPatternPrefix_inferenceProperties ready expectedBelow
        (by assumption)
        (by assumption) (by assumption) (by rfl) (by rfl)
  case case5 =>
    intros
    unfold MatchPatternFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      exact integerPatternPrefix_inferenceProperties ready expectedBelow
        (by assumption)
        (by assumption) (by assumption) (by rfl) (by rfl)
  -- Parenthesized/grouped expression.
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold MatchPatternFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have constructorPrefix :=
          contextualConstructorPrefix_inferenceProperties ready expectedBelow
            validated (by assumption) (by assumption)
        have children := childrenIH _ _ _ constructorPrefix.2.1
          constructorPrefix.2.2 validated (by assumption)
        exact ⟨constructorPrefix.1.trans children.1, children.2⟩
      | have constructorPrefix :=
          explicitConstructorPrefix_inferenceProperties ready expectedBelow
            validated (by assumption) (by rfl) (by assumption)
        have children := childrenIH _ _ _ constructorPrefix.2.1
          constructorPrefix.2.2 validated (by assumption)
        exact ⟨constructorPrefix.1.trans children.1, children.2⟩
  -- Tuple expression.
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold MatchPatternFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have constructorPrefix :=
          contextualConstructorPrefix_inferenceProperties ready expectedBelow
            validated (by assumption) (by assumption)
        have children := childrenIH _ _ _ constructorPrefix.2.1
          constructorPrefix.2.2 validated (by assumption)
        exact ⟨constructorPrefix.1.trans children.1, children.2⟩
      | have constructorPrefix :=
          explicitConstructorPrefix_inferenceProperties ready expectedBelow
            validated (by assumption) (by rfl) (by assumption)
        have children := childrenIH _ _ _ constructorPrefix.2.1
          constructorPrefix.2.2 validated (by assumption)
        exact ⟨constructorPrefix.1.trans children.1, children.2⟩
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold MatchPatternFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    have argumentTypesEq :
        (freshTypes sources.length inputState).1 = argumentTypes := by
      simpa only using congrArg Prod.fst freshEq
    have allocatedStateEq :
        (freshTypes sources.length inputState).2 = allocatedState := by
      simpa only using congrArg Prod.snd freshEq
    have tuplePrefix := tuplePatternPrefix_inferenceProperties
      (count := sources.length) (elementTypes := argumentTypes)
      (allocated := allocatedState) ready expectedBelow freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have children := childrenIH _ _ tuplePrefix.2.1 tuplePrefix.2.2 validated
      (by
        rw [← argumentTypesEq]
        simpa only [sources] using (by assumption))
    exact ⟨tuplePrefix.1.trans children.1, children.2⟩
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold MatchPatternsFlatInferenceProperties
    unfold MatchPatternFlatInferenceProperties at ihHead
    unfold MatchPatternsFlatInferenceProperties at ihTail
    intro result ready expectedBelow validated success
    simp only [inferMatchPatternsFlatFuel] at success
    cases headResult : inferMatchPatternFlatFuel fuel context head expectedHead
        seen state with
    | error error =>
        simp [headResult, bind, Except.bind] at success
    | ok inferredHead =>
        simp only [headResult, bind, Except.bind] at success
        cases tailResult : inferMatchPatternsFlatFuel fuel context rest
            expectedTail inferredHead.names inferredHead.state with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok inferredTail =>
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            have headProperties := ihHead inferredHead ready
              (expectedBelow expectedHead (by simp)) validated headResult
            have tailProperties := ihTail inferredHead inferredTail
              headProperties.2 (by
                intro expected member
                exact (expectedBelow expected (by simp [member])).weaken
                  headProperties.1.next_le) validated tailResult
            exact ⟨headProperties.1.trans tailProperties.1,
              tailProperties.2⟩
  all_goals
    intros
    first
      | unfold MatchPatternFlatInferenceProperties at *
      | unfold MatchPatternsFlatInferenceProperties at *
    intro result ready expectedBelow validated success
    first
      | unfold inferMatchPatternFlatFuel at success
      | unfold inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
    all_goals try simpa using ih1 _ (by assumption)
    all_goals try
      constructor
      · simpa only using State.InferenceProgress.refl ready.solved
      · simpa only using ready
    all_goals try exact (by simpa only using ih1 _ (by assumption))
    all_goals try exact State.InferenceProgress.refl ready.solved
    all_goals try
      exact binderPattern_inferenceProperties ready expectedBelow

/-- Successful source-pattern inference makes semantic inference progress,
preserves readiness, and returns a pattern type below the final allocator. -/
theorem inferMatchPatternFuel_inferenceProperties
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    state.InferenceProgress result.2 ∧ result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error =>
      simp [flatResult, bind, Except.bind] at success
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
      have properties :=
        inferMatchPatternFlatFuel_inferenceProperties_internal fuel context
          pattern expected [] state inferred ready expectedBelow validated
          flatResult
      exact ⟨properties.1, properties.2,
        properties.1.resolve_variablesBelow expectedBelow⟩

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

/-- Pattern traversal may enter binders in the current arm scope, but every
such allocation advances the declaration-local cutoff. -/
private theorem inferMatchPatternFlatFuel_advances_nextLocal
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    AdvancesNextLocal InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        AdvancesNextLocal InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        AdvancesNextLocal InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold AdvancesNextLocal at *
    intro result success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have childrenNext := childrenIH _ _ _ (by assumption)
        have unifiedNext := unify_preserves_nextLocal (by assumption)
        omega
      | have childrenNext := childrenIH _ _ _ (by assumption)
        have unifiedNext := unify_preserves_nextLocal (by assumption)
        simp_all <;> omega
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold AdvancesNextLocal at *
    intro result success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have childrenNext := childrenIH _ _ _ (by assumption)
        have unifiedNext := unify_preserves_nextLocal (by assumption)
        omega
      | have childrenNext := childrenIH _ _ _ (by assumption)
        have unifiedNext := unify_preserves_nextLocal (by assumption)
        simp_all <;> omega
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold AdvancesNextLocal at *
    intro result success
    unfold inferMatchPatternFlatFuel at success
    simp only [patternEq, sources, freshEq, bind, Except.bind] at success
    cases unifiedResult :
        unify allocatedState sourceExpected (Ty.productMany argumentTypes) with
    | error error =>
        simp [unifiedResult, bind, Except.bind] at success
    | ok unifiedState =>
        simp only [unifiedResult, bind, Except.bind] at success
        cases childrenResult : inferMatchPatternsFlatFuel sourceFuel context
            elements.elements argumentTypes sourceSeen unifiedState with
        | error error =>
            simp [childrenResult, bind, Except.bind] at success
        | ok children =>
            simp only [childrenResult, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            subst result
            have allocatedNext :=
              congrArg (fun pair => pair.2.nextLocal) freshEq
            have unifiedNext := unify_preserves_nextLocal unifiedResult
            have childrenNext := childrenIH unifiedState children (by
              simpa only [sources] using childrenResult)
            simp only [freshTypes_preserves_nextLocal] at allocatedNext
            exact calc
              inputState.nextLocal = allocatedState.nextLocal := allocatedNext
              _ = unifiedState.nextLocal := unifiedNext.symm
              _ ≤ children.state.nextLocal := childrenNext
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold AdvancesNextLocal at *
    intro result success
    simp only [inferMatchPatternsFlatFuel] at success
    cases headResult : inferMatchPatternFlatFuel fuel context head expectedHead
        seen state with
    | error error =>
        simp [headResult, bind, Except.bind] at success
    | ok inferredHead =>
        simp only [headResult, bind, Except.bind] at success
        cases tailResult : inferMatchPatternsFlatFuel fuel context rest
            expectedTail inferredHead.names inferredHead.state with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok inferredTail =>
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            exact Nat.le_trans (ihHead inferredHead headResult)
              (ihTail inferredHead inferredTail tailResult)
  all_goals
    intros
    unfold AdvancesNextLocal at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try have unifiedNext := unify_preserves_nextLocal (by assumption)
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.allocateBinder, bind, Except.bind]
    all_goals omega

private def PatternPreservesBinderBound (context : Context)
    (fuel : Nat) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result,
    state.LocalBindersBelowNextLocal →
    inferMatchPatternFlatFuel fuel context pattern expected seen state =
      .ok result →
    result.state.LocalBindersBelowNextLocal

private def PatternsPreserveBinderBound (context : Context)
    (fuel : Nat) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result,
    state.LocalBindersBelowNextLocal →
    inferMatchPatternsFlatFuel fuel context patterns expected seen state =
      .ok result →
    result.state.LocalBindersBelowNextLocal

private theorem unify_preserves_binder_bound_from_success
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next)
    (below : state.LocalBindersBelowNextLocal) :
    next.LocalBindersBelowNextLocal :=
  unify_preserves_localBindersBelowNextLocal below success

/- Flat pattern traversal preserves the stable local-identity bound while it
enters every binder introduced by the pattern. -/
set_option maxHeartbeats 1000000 in
theorem inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    ∀ result,
      state.LocalBindersBelowNextLocal →
      inferMatchPatternFlatFuel fuel context pattern expected seen state =
        .ok result →
      result.state.LocalBindersBelowNextLocal := by
  change PatternPreservesBinderBound context fuel pattern expected seen state
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := PatternPreservesBinderBound context)
      (motive2 := PatternsPreserveBinderBound context)
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _
          (unify_preserves_localBindersBelowNextLocal below (by assumption))
          (by assumption)
      | exact childrenIH _ _ _
          (unify_preserves_localBindersBelowNextLocal
            (freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal
              _ _ inputState below)
            (by assumption))
          (by assumption)
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | exact childrenIH _ _ _
          (unify_preserves_localBindersBelowNextLocal below (by assumption))
          (by assumption)
      | exact childrenIH _ _ _
          (unify_preserves_localBindersBelowNextLocal
            (freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal
              _ _ inputState below)
            (by assumption))
          (by assumption)
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp only [patternEq, sources, freshEq, bind, Except.bind] at success
    cases unifiedResult :
        unify allocatedState sourceExpected (Ty.productMany argumentTypes) with
    | error error =>
        simp [unifiedResult, bind, Except.bind] at success
    | ok unifiedState =>
        simp only [unifiedResult, bind, Except.bind] at success
        cases childrenResult : inferMatchPatternsFlatFuel sourceFuel context
            elements.elements argumentTypes sourceSeen unifiedState with
        | error error =>
            simp [childrenResult, bind, Except.bind] at success
        | ok children =>
            simp only [childrenResult, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            subst result
            have allocatedStateEq :
                (freshTypes sources.length inputState).2 = allocatedState :=
              congrArg Prod.snd freshEq
            have allocatedBelow :
                allocatedState.LocalBindersBelowNextLocal := by
              rw [← allocatedStateEq]
              exact freshTypes_preserves_localBindersBelowNextLocal
                sources.length inputState below
            exact childrenIH unifiedState children
              (unify_preserves_localBindersBelowNextLocal allocatedBelow
                unifiedResult)
              (by simpa only [sources] using childrenResult)
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsPreserveBinderBound at *
    unfold PatternPreservesBinderBound at ihHead
    intro result below success
    simp only [inferMatchPatternsFlatFuel] at success
    cases headResult : inferMatchPatternFlatFuel fuel context head expectedHead
        seen state with
    | error error =>
        simp [headResult, bind, Except.bind] at success
    | ok inferredHead =>
        simp only [headResult, bind, Except.bind] at success
        cases tailResult : inferMatchPatternsFlatFuel fuel context rest
            expectedTail inferredHead.names inferredHead.state with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok inferredTail =>
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            exact ihTail inferredHead inferredTail
              (ihHead inferredHead below headResult) tailResult
  case case3 =>
    intros
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try subst_vars
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      exact unify_preserves_binder_bound_from_success (by assumption) (by
          simpa [State.LocalBindersBelowNextLocal, State.fresh,
            State.addRequirementWithId] using below)
  case case5 =>
    intros
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try subst_vars
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      exact unify_preserves_binder_bound_from_success (by assumption) (by
          simpa [State.LocalBindersBelowNextLocal, State.fresh,
            State.addRequirementWithId] using below)
  case case9 =>
    intros
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try subst_vars
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      apply State.allocateBinder_preserves_localBindersBelowNextLocal
      exact below
  case case12 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel inner
      patternEq induction
    unfold PatternPreservesBinderBound at *
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp only [patternEq, bind, Except.bind] at success
    cases innerResult : inferMatchPatternFlatFuel sourceFuel context inner
        sourceExpected sourceSeen inputState with
    | error error => simp [innerResult, bind, Except.bind] at success
    | ok inferred =>
        simp only [innerResult, bind, Except.bind, pure, Pure.pure,
          Except.pure] at success
        injection success with resultEq
        subst result
        exact induction inferred below innerResult
  case case2 =>
    intros
    unfold PatternPreservesBinderBound
    intro result below success
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind, pure, Pure.pure, Except.pure]
    subst result
    exact below
  case case16 =>
    intros
    unfold PatternsPreserveBinderBound
    intro result below success
    simp only [inferMatchPatternsFlatFuel, pure, Pure.pure, Except.pure] at success
    injection success with resultEq
    subst result
    exact below
  all_goals
    intros
    first
      | unfold PatternPreservesBinderBound at *
      | unfold PatternsPreserveBinderBound at *
    intro result below success
    first
      | unfold inferMatchPatternFlatFuel at success
      | unfold inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    all_goals try subst_vars
    all_goals assumption

/-- Flat traversal of sibling patterns preserves the stable local-identity
bound across the source-ordered list. -/
theorem inferMatchPatternsFlatFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {patterns : List Syntax.Pattern}
    {expected : List Ty} {seen : List String} {state : State}
    {result : InferredPatterns}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferMatchPatternsFlatFuel fuel context patterns expected seen
      state = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  induction patterns generalizing expected seen state result with
  | nil =>
      cases expected with
      | nil =>
          simp only [inferMatchPatternsFlatFuel, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          subst result
          exact below
      | cons expected expectedTypes =>
          simp [inferMatchPatternsFlatFuel] at success
  | cons pattern patterns induction =>
      cases expected with
      | nil => simp [inferMatchPatternsFlatFuel] at success
      | cons expected expectedTypes =>
          simp only [inferMatchPatternsFlatFuel] at success
          cases headResult : inferMatchPatternFlatFuel fuel context pattern
              expected seen state with
          | error error =>
              simp [headResult, bind, Except.bind] at success
          | ok inferredHead =>
              simp only [headResult, bind, Except.bind] at success
              cases tailResult : inferMatchPatternsFlatFuel fuel context
                  patterns expectedTypes inferredHead.names inferredHead.state
                  with
              | error error =>
                  simp [tailResult, bind, Except.bind] at success
              | ok inferredTail =>
                  simp only [tailResult, bind, Except.bind, pure, Pure.pure,
                    Except.pure] at success
                  have tailBelow := induction (result := inferredTail)
                    (inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
                      fuel context pattern expected seen state inferredHead below
                      headResult)
                    tailResult
                  injection success with resultEq
                  subst result
                  exact tailBelow

/-- Successful flat inference of one pattern preserves the declaration-scoped
state header for every incoming binder-name accumulator. -/
theorem inferMatchPatternFlatFuel_state_header
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {state : State}
    {result : InferredPattern}
    (success : inferMatchPatternFlatFuel fuel context pattern expected seen
      state = .ok result) :
    result.state.header = state.header :=
  inferMatchPatternFlatFuel_preserves_header fuel context pattern expected seen
    state result success

/-- Successful flat inference of sibling patterns preserves the same
declaration-scoped state header. -/
theorem inferMatchPatternsFlatFuel_state_header
    {fuel : Nat} {context : Context} {patterns : List Syntax.Pattern}
    {expected : List Ty} {seen : List String} {state : State}
    {result : InferredPatterns}
    (success : inferMatchPatternsFlatFuel fuel context patterns expected seen
      state = .ok result) :
    result.state.header = state.header := by
  induction patterns generalizing expected seen state result with
  | nil =>
      cases expected with
      | nil =>
          simp only [inferMatchPatternsFlatFuel, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          subst result
          rfl
      | cons expected expectedTypes =>
          simp [inferMatchPatternsFlatFuel] at success
  | cons pattern patterns induction =>
      cases expected with
      | nil => simp [inferMatchPatternsFlatFuel] at success
      | cons expected expectedTypes =>
          simp only [inferMatchPatternsFlatFuel] at success
          cases headResult : inferMatchPatternFlatFuel fuel context pattern
              expected seen state with
          | error error =>
              simp [headResult, bind, Except.bind] at success
          | ok inferredHead =>
              simp only [headResult, bind, Except.bind] at success
              cases tailResult : inferMatchPatternsFlatFuel fuel context
                  patterns expectedTypes inferredHead.names inferredHead.state
                  with
              | error error =>
                  simp [tailResult, bind, Except.bind] at success
              | ok inferredTail =>
                  simp only [tailResult, bind, Except.bind, pure, Pure.pure,
                    Except.pure] at success
                  have tailHeader := induction (result := inferredTail)
                    tailResult
                  injection success with resultEq
                  subst result
                  exact tailHeader.trans
                    (inferMatchPatternFlatFuel_state_header headResult)

/-- The complete algorithmic state package needed by source-pattern
soundness, with no assumption about the incoming `seen` accumulator. -/
theorem inferMatchPatternFlatFuel_stateProperties
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {state : State}
    {result : InferredPattern}
    (ready : state.InferenceReady)
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (below : state.LocalBindersBelowNextLocal)
    (success : inferMatchPatternFlatFuel fuel context pattern expected seen
      state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.state.LocalBindersBelowNextLocal ∧
      result.state.owner = state.owner := by
  have inference := inferMatchPatternFlatFuel_inferenceProperties_internal
    fuel context pattern expected seen state result ready expectedBelow
    validated success
  have header := inferMatchPatternFlatFuel_state_header success
  exact ⟨inference.1, inference.2,
    inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
      fuel context pattern expected seen state result below success,
    congrArg (fun stable : State.Header => stable.owner) header⟩

/-- The corresponding algorithmic state package for a source-ordered list of
sibling patterns. -/
theorem inferMatchPatternsFlatFuel_stateProperties
    {fuel : Nat} {context : Context} {patterns : List Syntax.Pattern}
    {expected : List Ty} {seen : List String} {state : State}
    {result : InferredPatterns}
    (ready : state.InferenceReady)
    (expectedBelow : ∀ type ∈ expected,
      type.VariablesBelow state.inference.next)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (below : state.LocalBindersBelowNextLocal)
    (success : inferMatchPatternsFlatFuel fuel context patterns expected seen
      state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.state.LocalBindersBelowNextLocal ∧
      result.state.owner = state.owner := by
  induction patterns generalizing expected seen state result with
  | nil =>
      cases expected with
      | nil =>
          simp only [inferMatchPatternsFlatFuel, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          subst result
          exact ⟨State.InferenceProgress.refl ready.solved, ready, below, rfl⟩
      | cons expected expectedTypes =>
          simp [inferMatchPatternsFlatFuel] at success
  | cons pattern patterns induction =>
      cases expected with
      | nil => simp [inferMatchPatternsFlatFuel] at success
      | cons expected expectedTypes =>
          simp only [inferMatchPatternsFlatFuel] at success
          cases headResult : inferMatchPatternFlatFuel fuel context pattern
              expected seen state with
          | error error =>
              simp [headResult, bind, Except.bind] at success
          | ok inferredHead =>
              simp only [headResult, bind, Except.bind] at success
              cases tailResult : inferMatchPatternsFlatFuel fuel context
                  patterns expectedTypes inferredHead.names inferredHead.state
                  with
              | error error =>
                  simp [tailResult, bind, Except.bind] at success
              | ok inferredTail =>
                  simp only [tailResult, bind, Except.bind, pure, Pure.pure,
                    Except.pure] at success
                  have headProperties :=
                    inferMatchPatternFlatFuel_stateProperties ready
                      (expectedBelow expected (by simp)) validated below
                      headResult
                  have tailProperties := induction
                    (expected := expectedTypes) (seen := inferredHead.names)
                    (state := inferredHead.state) (result := inferredTail)
                    headProperties.2.1 (by
                      intro type member
                      exact (expectedBelow type (by simp [member])).weaken
                        headProperties.1.next_le)
                    headProperties.2.2.1 tailResult
                  injection success with resultEq
                  subst result
                  exact ⟨headProperties.1.trans tailProperties.1,
                    tailProperties.2.1, tailProperties.2.2.1,
                    tailProperties.2.2.2.trans headProperties.2.2.2⟩

/-- A successful direct literal-pattern branch exposes its exact retained
source, resolution, instruction, requirement, and unchanged binder scope.
The resolved target equality is the only type-inference fact needed by the
declarative integer-pattern bridge. -/
theorem inferMatchPatternFlatFuel_literal_facts
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {literal : Syntax.CoreLiteral} {expected : Ty} {seen : List String}
    {state : State} {result : InferredPattern}
    (patternValue : pattern.value = .literal literal)
    (progress : state.InferenceProgress result.state)
    (success : inferMatchPatternFlatFuel fuel context pattern expected seen
      state = .ok result) :
    ∃ source resolution,
      literal.value = source ∧
      result.source = .integerLiteral pattern.span literal ∧
      result.resolution = .integerLiteral source resolution ∧
      result.instructions = [.integerLiteral source resolution] ∧
      result.requirements = [resolution.requirement] ∧
      result.names = seen ∧
      result.state.localBinders = state.localBinders ∧
      result.state.resolve resolution.targetType =
        result.state.resolve expected := by
  cases fuel with
  | zero => simp [inferMatchPatternFlatFuel] at success
  | succ fuel =>
      unfold inferMatchPatternFlatFuel at success
      simp only [patternValue] at success
      cases literalValue : literal.value with
      | string spelling => simp [literalValue] at success
      | decimal spelling | hexadecimal spelling =>
          simp only [literalValue, bind, Except.bind] at success
          cases decoded : Frontend.numericLiteralValue? literal.value with
          | none =>
              rw [literalValue] at decoded
              simp [decoded] at success
          | some rawValue =>
              rw [literalValue] at decoded
              simp only [decoded] at success
              simp [State.fresh, TypeSystem.InferState.fresh,
                State.addRequirementWithId] at success
              repeat' first | split at success
              all_goals try simp_all only [exceptPure_eq_ok]
              all_goals try simp_all
              all_goals try cases success
              all_goals try subst result
              all_goals
                have unified := unify_resolve_eq (by assumption)
                have bindersPreserved :=
                  unify_preserves_localBinders (by assumption)
                simp_all [State.resolve, TypeSystem.InferState.resolve,
                  State.fresh, TypeSystem.InferState.fresh,
                  State.addRequirementWithId]
                have extension := progress.substitution_extends expected
                simp_all only [State.resolve,
                  TypeSystem.InferState.resolve]

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

/-- Successful nested-pattern inference preserves or advances the shared
declaration-local cutoff. -/
theorem inferMatchPatternFuel_nextLocal_le
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    state.nextLocal ≤ result.2.nextLocal := by
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
      exact inferMatchPatternFlatFuel_advances_nextLocal fuel context pattern
        expected [] state inferred flatResult

@[simp] theorem inferMatchPatternFuel_preserves_owner
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    result.2.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferMatchPatternFuel_state_header success)

@[simp] theorem inferMatchPatternFuel_preserves_inputs
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    result.2.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferMatchPatternFuel_state_header success)

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

private theorem inferUnaryOperator_lexicalScope
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.lexicalScope = state.lexicalScope := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have firstUnifiedScope : v.lexicalScope = state.lexicalScope :=
    unify_preserves_lexicalScope heq
  all_goals try have secondUnifiedScope :
      v_1.lexicalScope = v.lexicalScope :=
    unify_preserves_lexicalScope heq_1
  all_goals try have unifiedScope :=
    unify_preserves_lexicalScope (by assumption)
  all_goals simp_all [pure, Pure.pure, Except.pure, State.lexicalScope,
    State.addRequirementsWithIds, State.addRequirementWithId]
  all_goals grind [unify_preserves_lexicalScope]

private theorem inferUnaryOperator_nextLocal
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.nextLocal = state.nextLocal := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have firstUnifiedNext : v.nextLocal = state.nextLocal :=
    unify_preserves_nextLocal heq
  all_goals try have secondUnifiedNext :
      v_1.nextLocal = v.nextLocal :=
    unify_preserves_nextLocal heq_1
  all_goals try have unifiedNext :=
    unify_preserves_nextLocal (by assumption)
  all_goals simp_all [pure, Pure.pure, Except.pure,
    State.addRequirementsWithIds, State.addRequirementWithId]
  all_goals grind [unify_preserves_nextLocal]

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

private theorem inferBinaryOperator_lexicalScope
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.lexicalScope = state.lexicalScope := by
  unfold inferBinaryOperator at success
  simp only [bind, Except.bind] at success
  cases firstResult : unify state left right with
  | error error =>
      simp [firstResult, bind, Except.bind] at success
  | ok firstState =>
      simp only [firstResult, bind, Except.bind] at success
      have firstScope := unify_preserves_lexicalScope firstResult
      repeat' first | split at success
      all_goals try cases success
      all_goals try have secondScope :=
        unify_preserves_lexicalScope (by assumption)
      all_goals simp_all [pure, Pure.pure, Except.pure,
        State.lexicalScope, State.addRequirementsWithIds,
        State.addRequirementWithId]
      all_goals grind [unify_preserves_lexicalScope]

private theorem inferBinaryOperator_nextLocal
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.nextLocal = state.nextLocal := by
  unfold inferBinaryOperator at success
  simp only [bind, Except.bind] at success
  cases firstResult : unify state left right with
  | error error =>
      simp [firstResult, bind, Except.bind] at success
  | ok firstState =>
      simp only [firstResult, bind, Except.bind] at success
      have firstNext := unify_preserves_nextLocal firstResult
      repeat' first | split at success
      all_goals try cases success
      all_goals try have secondNext :=
        unify_preserves_nextLocal (by assumption)
      all_goals simp_all [pure, Pure.pure, Except.pure,
        State.addRequirementsWithIds, State.addRequirementWithId]
      all_goals grind [unify_preserves_nextLocal]

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

private theorem candidateWithExpected_some_lexicalScope
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.lexicalScope = state.lexicalScope := by
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
      exact withExpected_lexicalScope fittedResult

private theorem candidateWithExpected_some_nextLocal
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.nextLocal = state.nextLocal := by
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
      exact withExpected_nextLocal fittedResult

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

private theorem fitArguments_some_lexicalScope
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.lexicalScope = state.lexicalScope := by
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
                            (candidateWithExpected_some_lexicalScope fittedResult)

private theorem fitArguments_some_nextLocal
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.nextLocal = state.nextLocal := by
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
                            (candidateWithExpected_some_nextLocal fittedResult)

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

private theorem tryFunctionCandidate_some_lexicalScope
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.lexicalScope = state.lexicalScope := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fitScope :=
    fitArguments_some_lexicalScope (by assumption)
  all_goals try have expectedScope :=
    candidateWithExpected_some_lexicalScope (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.lexicalScope, State.addRequirementsWithIds,
    State.addRequirementWithId, State.markDirectCallRequirements]

private theorem tryFunctionCandidate_some_nextLocal
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.nextLocal = state.nextLocal := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fitNext :=
    fitArguments_some_nextLocal (by assumption)
  all_goals try have expectedNext :=
    candidateWithExpected_some_nextLocal (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.addRequirementsWithIds,
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

/-- A successful candidate attempt checked against a concrete expectation
retains that equality after its bookkeeping-only requirement allocations. -/
private theorem tryFunctionCandidate_some_apply_eq
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    {outer : Substitution}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call (some expected) state signature = .ok (some result))
    (extension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    outer.apply result.result.type = outer.apply expected := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advancedState : State := {
    state with inference := {
      state.inference with next := instantiated.next
    }
  }
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
      cases parametersResult : parameterTypesForArity?
          signature.parameterTypes.length parameterType with
      | none => simp [parametersResult] at success
      | some parameterTypes =>
          simp only [parametersResult] at success
          cases argumentsResult : fitArguments context advancedState arguments
              parameterTypes with
          | error error =>
              simp [instantiated, advancedState, argumentsResult, bind,
                Except.bind] at success
          | ok fittedArgumentsOption =>
              cases fittedArgumentsOption with
              | none =>
                  simp [instantiated, advancedState, argumentsResult, bind,
                    Except.bind] at success
              | some fittedArguments =>
                  simp only [instantiated, advancedState, argumentsResult,
                    bind, Except.bind] at success
                  cases fittedResultResult : candidateWithExpected context
                      fittedArguments.state { id := call, type := resultType }
                      (some expected) with
                  | error error =>
                      simp [fittedResultResult, bind, Except.bind] at success
                  | ok fittedResultOption =>
                      cases fittedResultOption with
                      | none =>
                          simp [fittedResultResult, bind, Except.bind]
                            at success
                      | some fittedResult =>
                          simp only [fittedResultResult, bind, Except.bind]
                            at success
                          cases integerValidation :
                              validateCandidateIntegerLiterals context
                                fittedResult.state integerLiteralOrigins with
                          | error error =>
                              simp [integerValidation, bind, Except.bind]
                                at success
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
                                  have finalStateInference :
                                      finalState.inference =
                                        fittedResult.state.inference := by
                                    simp only [finalState, allocation,
                                      State.markDirectCallRequirements,
                                      addRequirementsWithIds_inference]
                                  have fittedExtension :
                                      outer.SemanticallyExtends
                                        fittedResult.state.inference.substitution := by
                                    change outer.SemanticallyExtends
                                      finalState.inference.substitution at extension
                                    rw [finalStateInference] at extension
                                    exact extension
                                  change outer.apply
                                      (finalState.resolve
                                        fittedResult.expression.type) =
                                    outer.apply expected
                                  calc
                                    outer.apply (finalState.resolve
                                        fittedResult.expression.type) =
                                        outer.apply fittedResult.expression.type :=
                                      by
                                        calc
                                          outer.apply (finalState.resolve
                                              fittedResult.expression.type) =
                                              outer.apply
                                                (fittedResult.state.resolve
                                                  fittedResult.expression.type) := by
                                            congr 1
                                            change finalState.inference.resolve
                                                fittedResult.expression.type =
                                              fittedResult.state.inference.resolve
                                                fittedResult.expression.type
                                            rw [finalStateInference]
                                          _ = outer.apply
                                              fittedResult.expression.type := by
                                            simpa only [State.resolve,
                                              TypeSystem.InferState.resolve]
                                              using fittedExtension
                                                fittedResult.expression.type
                                    _ = outer.apply expected :=
                                      candidateWithExpected_some_apply_eq
                                        fittedResultResult fittedExtension

/-- Overload ranking can only retain an unchanged successful attempt, so the
selected result also agrees with its concrete expectation. -/
private theorem selectFunctionCandidateFrom_some_apply_eq
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Ty} {state : State}
    {result : CandidateAttemptResult} {outer : Substitution}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call (some expected) state = .ok result)
    (extension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    outer.apply result.result.type = outer.apply expected := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_some_apply_eq candidateSuccess extension

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

private theorem selectFunctionCandidateFrom_lexicalScope
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.lexicalScope = state.lexicalScope := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_some_lexicalScope candidateSuccess

private theorem selectFunctionCandidateFrom_nextLocal
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.nextLocal = state.nextLocal := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_some_nextLocal candidateSuccess

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

@[simp] private theorem attachExpressionCoercions_lexicalScope
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).lexicalScope =
      state.lexicalScope := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction _).trans (by rfl)

@[simp] private theorem attachExpressionCoercions_nextLocal
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).nextLocal =
      state.nextLocal := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction _).trans (by rfl)

@[simp] private theorem allocateExpressionId_inference
    (state : State) :
    state.allocateExpressionId.2.inference = state.inference := by
  rfl

@[simp] private theorem allocateExpressionId_lexicalScope
    (state : State) :
    state.allocateExpressionId.2.lexicalScope = state.lexicalScope := by
  rfl

@[simp] private theorem allocateExpressionId_nextLocal
    (state : State) :
    state.allocateExpressionId.2.nextLocal = state.nextLocal := by
  rfl

@[simp] private theorem attachExpressionCoercions_resolve
    (state : State) (entries : List ExpressionCoercions) (type : Ty) :
    (attachExpressionCoercions state entries).resolve type =
      state.resolve type := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      rw [induction]
      rfl

@[simp] private theorem attachExpressionCoercions_inference
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).inference = state.inference := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      rw [induction]
      rfl

@[simp] private theorem recordSelectedCall_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.header =
    attempt.state.header := by
  simp [recordSelectedCall, recordSelectedCallResult]

@[simp] private theorem recordSelectedCall_lexicalScope
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.lexicalScope =
      attempt.state.lexicalScope := by
  simp [recordSelectedCall, recordSelectedCallResult]

@[simp] private theorem recordSelectedCall_nextLocal
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.nextLocal =
      attempt.state.nextLocal := by
  simp [recordSelectedCall, recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.header = state.header := by
  simp [recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_lexicalScope
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.lexicalScope = state.lexicalScope := by
  simp [recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_nextLocal
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.nextLocal = state.nextLocal := by
  simp [recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_resolve
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) (type : Ty) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.resolve type = state.resolve type := by
  unfold recordSelectedCallResult
  simp only [recordExpression, State.recordNode, State.resolve,
    TypeSystem.InferState.resolve, allocateExpressionId_inference,
    attachExpressionCoercions_inference]

@[simp] private theorem recordSelectedCallResult_inference
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.inference = state.inference := by
  unfold recordSelectedCallResult
  simp only [recordExpression, State.recordNode,
    allocateExpressionId_inference, attachExpressionCoercions_inference]

@[simp] private theorem recordSelectedCall_resolve
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (type : Ty) :
    (recordSelectedCall source callee name arguments attempt).2.resolve type =
      attempt.state.resolve type := by
  simp [recordSelectedCall]

@[simp] private theorem recordSelectedCall_inference
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.inference =
      attempt.state.inference := by
  simp only [recordSelectedCall, recordSelectedCallResult_inference]

/-- Recording a successfully selected direct call changes only source
metadata, so the selected expected-type equality is retained. -/
private theorem recordSelectedCall_selected_apply_eq
    {context : Context} {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Ty} {state : State}
    {attempt : CandidateAttemptResult} {outer : Substitution}
    (selected : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call (some expected) state = .ok attempt)
    (extension : outer.SemanticallyExtends
      (recordSelectedCall source callee name arguments attempt).2.inference.substitution) :
    outer.apply
        (recordSelectedCall source callee name arguments attempt).1.type =
      outer.apply expected := by
  have attemptExtension : outer.SemanticallyExtends
      attempt.state.inference.substitution := by
    simpa only [recordSelectedCall_inference] using extension
  change outer.apply attempt.result.type = outer.apply expected
  exact selectFunctionCandidateFrom_some_apply_eq selected attemptExtension

/-- The binary-overload suffix performs one final fit after overload
selection.  Recording the fitted result preserves that final equality. -/
private theorem recordSelectedCallResult_withExpected_apply_eq
    {context : Context} {source callee : Syntax.Expr} {name : String}
    {arguments : List InferredExpression} {attempt : CandidateAttemptResult}
    {actual : InferredExpression} {expected : Ty} {state : State}
    {fitted : ExpectationResult} {outer : Substitution}
    (fittedSuccess : withExpected context state actual (some expected) =
      .ok fitted)
    (extension : outer.SemanticallyExtends
      (recordSelectedCallResult source callee name arguments attempt
        fitted.expression fitted.coercions fitted.state).2.inference.substitution) :
    outer.apply
        (recordSelectedCallResult source callee name arguments attempt
          fitted.expression fitted.coercions fitted.state).1.type =
      outer.apply expected := by
  have fittedExtension : outer.SemanticallyExtends
      fitted.state.inference.substitution := by
    simpa only [recordSelectedCallResult_inference] using extension
  change outer.apply fitted.expression.type = outer.apply expected
  exact withExpected_some_apply_eq fittedSuccess fittedExtension

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

/-- Successful indirect application against a concrete expectation returns a
result equal to that expectation under every semantic extension of its final
inference substitution. -/
private theorem applyFunctionType_some_apply_eq
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Ty} {state : State}
    {result : IndirectApplicationResult} {outer : Substitution}
    (success : applyFunctionType context call calleeType arguments
      (some expected) state = .ok result)
    (extension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    outer.apply result.result.type = outer.apply expected := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany
              (arguments.map (fun argument => argument.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } (some expected) with
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
              exact withExpected_some_apply_eq resultResult extension
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany
            (arguments.map fun argument => argument.type)) resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } (some expected) with
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
              exact withExpected_some_apply_eq resultResult extension

/-- Every parameter of a compiler-provided function is a closed builtin type,
so it lies below every flexible-variable allocator bound. -/
private theorem builtinFunction_parameterTypes_variablesBelow
    (function : BuiltinFunctionId) (next : Nat) :
    ∀ type ∈ function.parameterTypes, type.VariablesBelow next := by
  cases function <;>
    simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word, Ty.bool]

/-- The result of a compiler-provided function is a closed builtin type. -/
private theorem builtinFunction_returnType_variablesBelow
    (function : BuiltinFunctionId) (next : Nat) :
    function.returnType.VariablesBelow next := by
  cases function <;>
    simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

/-- Consequently, the complete monomorphic type of a compiler-provided
function is allocator-bounded at every bound. -/
private theorem builtinFunction_type_variablesBelow
    (function : BuiltinFunctionId) (next : Nat) :
    function.type.VariablesBelow next := by
  unfold BuiltinFunctionId.type
  exact (Ty.variablesBelow_function_iff _ _ _).2 ⟨
    Ty.variablesBelow_productMany
      (builtinFunction_parameterTypes_variablesBelow function next),
    builtinFunction_returnType_variablesBelow function next⟩

/-- Pairwise builtin-argument unification makes semantic inference progress
and preserves readiness when both input rows are allocator-bounded.  The
underlying operation deliberately stops when either row is exhausted. -/
theorem unifyBuiltinFunctionArgumentsEqual_inferenceProperties
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters,
      parameter.VariablesBelow state.inference.next)
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      exact ⟨.refl ready.solved, ready⟩
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          exact ⟨.refl ready.solved, ready⟩
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unifiedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have argumentBelow := argumentsBelow argument (by simp)
              have parameterBelow := parametersBelow parameter (by simp)
              have headProgress := unify_inferenceProgress ready.solved
                argumentBelow parameterBelow unifyResult
              have headReady := unify_preserves_inferenceReady ready
                argumentBelow parameterBelow unifyResult
              have tailArgumentsBelow : ∀ tail ∈ arguments,
                  tail.type.VariablesBelow
                    unifiedState.inference.next := by
                intro tail member
                exact (argumentsBelow tail (by simp [member])).weaken
                  headProgress.next_le
              have tailParametersBelow : ∀ tail ∈ parameters,
                  tail.VariablesBelow unifiedState.inference.next := by
                intro tail member
                exact (parametersBelow tail (by simp [member])).weaken
                  headProgress.next_le
              have tailProperties := induction headReady tailArgumentsBelow
                tailParametersBelow success
              exact ⟨headProgress.trans tailProperties.1,
                tailProperties.2⟩

/-- Allocating and recording the synthetic callee of a builtin call changes
only source metadata.  Its closed result type therefore remains bounded. -/
private theorem recordBuiltinFunctionCall_tail_inferenceProperties
    (source callee : Syntax.Expr) (name : String)
    (function : BuiltinFunctionId) (arguments : List InferredExpression)
    (call : ExpressionId) (state : State) (ready : state.InferenceReady) :
    let allocation := state.allocateExpressionId
    let calleeExpression : InferredExpression := {
      id := allocation.1
      type := function.type
    }
    let calleeRecord := recordExpression callee calleeExpression
      (.reference name (.builtinFunction function)) [] [] allocation.2
    let result : InferredExpression := {
      id := call
      type := calleeRecord.2.resolve function.returnType
    }
    let callRecord := recordExpression source result
      (.call allocation.1 (arguments.map (fun argument => argument.id))
        (.builtinFunction function)) [] [] calleeRecord.2
    state.InferenceProgress callRecord.2 ∧
      callRecord.2.InferenceReady ∧
      callRecord.1.type.VariablesBelow callRecord.2.inference.next := by
  let allocation := state.allocateExpressionId
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := function.type
  }
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.builtinFunction function)) [] [] allocation.2
  let result : InferredExpression := {
    id := call
    type := calleeRecord.2.resolve function.returnType
  }
  let callRecord := recordExpression source result
    (.call allocation.1 (arguments.map (fun argument => argument.id))
      (.builtinFunction function)) [] [] calleeRecord.2
  change state.InferenceProgress callRecord.2 ∧
    callRecord.2.InferenceReady ∧
    callRecord.1.type.VariablesBelow callRecord.2.inference.next
  have allocatedProgress : state.InferenceProgress allocation.2 :=
    State.InferenceProgress.allocateExpressionId state ready.solved
  have allocatedReady : allocation.2.InferenceReady :=
    State.InferenceReady.allocateExpressionId ready
  have calleeProgress : allocation.2.InferenceProgress calleeRecord.2 := by
    simpa only [calleeRecord, recordExpression] using
      State.InferenceProgress.recordNode allocation.2 (.expression {
        id := calleeExpression.id
        span := callee.span
        type := calleeExpression.type
        form := .reference name (.builtinFunction function)
        requirements := []
        coercions := []
      }) allocatedReady.solved
  have calleeReady : calleeRecord.2.InferenceReady := by
    simpa only [calleeRecord, recordExpression] using
      State.InferenceReady.recordNode (.expression {
        id := calleeExpression.id
        span := callee.span
        type := calleeExpression.type
        form := .reference name (.builtinFunction function)
        requirements := []
        coercions := []
      }) allocatedReady
  have resultBelow : result.type.VariablesBelow
      calleeRecord.2.inference.next := by
    exact calleeReady.solved.variablesBelow_apply
      (builtinFunction_returnType_variablesBelow function _)
  have callProgress : calleeRecord.2.InferenceProgress callRecord.2 := by
    simpa only [callRecord, recordExpression] using
      State.InferenceProgress.recordNode calleeRecord.2 (.expression {
        id := result.id
        span := source.span
        type := result.type
        form := .call allocation.1
          (arguments.map (fun argument => argument.id))
          (.builtinFunction function)
        requirements := []
        coercions := []
      }) calleeReady.solved
  have callReady : callRecord.2.InferenceReady := by
    simpa only [callRecord, recordExpression] using
      State.InferenceReady.recordNode (.expression {
        id := result.id
        span := source.span
        type := result.type
        form := .call allocation.1
          (arguments.map (fun argument => argument.id))
          (.builtinFunction function)
        requirements := []
        coercions := []
      }) calleeReady
  have totalProgress := allocatedProgress.trans
    (calleeProgress.trans callProgress)
  have returnedBelow : callRecord.1.type.VariablesBelow
      callRecord.2.inference.next := by
    simpa only [callRecord, recordExpression] using
      resultBelow.weaken callProgress.next_le
  exact ⟨totalProgress, callReady, returnedBelow⟩

/-- Recording a fixed compiler-function call inherits pairwise unification
progress, optional expected-type unification, and the metadata-only recording
guarantees of its synthetic callee and call nodes. -/
theorem recordBuiltinFunctionCall_inferenceProperties
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  unfold recordBuiltinFunctionCall at success
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [arity, ↓reduceIte, bind, Except.bind] at success
    cases argumentsResult :
        unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes
          state with
    | error error =>
        simp [argumentsResult, bind, Except.bind] at success
    | ok argumentsState =>
        simp only [argumentsResult, bind, Except.bind] at success
        have argumentsProperties :=
          unifyBuiltinFunctionArgumentsEqual_inferenceProperties ready
            argumentsBelow
            (builtinFunction_parameterTypes_variablesBelow function _)
            argumentsResult
        cases expected with
        | none =>
            simp only at success
            let allocation := argumentsState.allocateExpressionId
            let calleeExpression : InferredExpression := {
              id := allocation.1
              type := function.type
            }
            let calleeRecord := recordExpression callee calleeExpression
              (.reference name (.builtinFunction function)) [] [] allocation.2
            let returned : InferredExpression := {
              id := call
              type := calleeRecord.2.resolve function.returnType
            }
            let callRecord := recordExpression source returned
              (.call allocation.1
                (arguments.map (fun argument => argument.id))
                (.builtinFunction function)) [] [] calleeRecord.2
            change Except.ok callRecord = Except.ok result at success
            injection success with resultEq
            subst result
            have tailProperties :=
              recordBuiltinFunctionCall_tail_inferenceProperties source callee
                name function arguments call argumentsState
                argumentsProperties.2
            change state.InferenceProgress callRecord.2 ∧
              callRecord.2.InferenceReady ∧
              callRecord.1.type.VariablesBelow callRecord.2.inference.next
            exact ⟨argumentsProperties.1.trans tailProperties.1,
              tailProperties.2⟩
        | some expectedType =>
            cases expectedResult :
                unify argumentsState function.returnType expectedType with
            | error error =>
                simp [expectedResult, bind, Except.bind] at success
            | ok fittedState =>
                simp only [expectedResult, bind, Except.bind] at success
                have expectedAtArguments : expectedType.VariablesBelow
                    argumentsState.inference.next :=
                  (expectedBelow expectedType (by simp)).weaken
                    argumentsProperties.1.next_le
                have expectedProgress := unify_inferenceProgress
                  argumentsProperties.2.solved
                  (builtinFunction_returnType_variablesBelow function _)
                  expectedAtArguments expectedResult
                have fittedReady := unify_preserves_inferenceReady
                  argumentsProperties.2
                  (builtinFunction_returnType_variablesBelow function _)
                  expectedAtArguments expectedResult
                let allocation := fittedState.allocateExpressionId
                let calleeExpression : InferredExpression := {
                  id := allocation.1
                  type := function.type
                }
                let calleeRecord := recordExpression callee calleeExpression
                  (.reference name (.builtinFunction function)) [] []
                    allocation.2
                let returned : InferredExpression := {
                  id := call
                  type := calleeRecord.2.resolve function.returnType
                }
                let callRecord := recordExpression source returned
                  (.call allocation.1
                    (arguments.map (fun argument => argument.id))
                    (.builtinFunction function)) [] [] calleeRecord.2
                change Except.ok callRecord = Except.ok result at success
                injection success with resultEq
                subst result
                have tailProperties :=
                  recordBuiltinFunctionCall_tail_inferenceProperties source
                    callee name function arguments call fittedState fittedReady
                change state.InferenceProgress callRecord.2 ∧
                  callRecord.2.InferenceReady ∧
                  callRecord.1.type.VariablesBelow
                    callRecord.2.inference.next
                exact ⟨argumentsProperties.1.trans
                    (expectedProgress.trans tailProperties.1),
                  tailProperties.2⟩
  · simp [arity, bind, Except.bind] at success

/-- A fixed compiler-function call explicitly unifies its closed return type
with the supplied expectation before recording metadata. -/
private theorem recordBuiltinFunctionCall_some_apply_eq
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Ty} {state : State}
    {result : InferredExpression × State} {outer : Substitution}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call (some expected) state = .ok result)
    (extension : outer.SemanticallyExtends
      result.2.inference.substitution) :
    outer.apply result.1.type = outer.apply expected := by
  unfold recordBuiltinFunctionCall at success
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [arity, ↓reduceIte, bind, Except.bind] at success
    cases argumentsResult :
        unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes
          state with
    | error error =>
        simp [argumentsResult, bind, Except.bind] at success
    | ok argumentsState =>
        simp only [argumentsResult, bind, Except.bind] at success
        cases expectedResult :
            unify argumentsState function.returnType expected with
        | error error =>
            simp [expectedResult, bind, Except.bind] at success
        | ok fittedState =>
            simp only [expectedResult, bind, Except.bind] at success
            let allocation := fittedState.allocateExpressionId
            let calleeExpression : InferredExpression := {
              id := allocation.1
              type := function.type
            }
            let calleeRecord := recordExpression callee calleeExpression
              (.reference name (.builtinFunction function)) [] [] allocation.2
            let returned : InferredExpression := {
              id := call
              type := calleeRecord.2.resolve function.returnType
            }
            let callRecord := recordExpression source returned
              (.call allocation.1
                (arguments.map (fun argument => argument.id))
                (.builtinFunction function)) [] [] calleeRecord.2
            change Except.ok callRecord = Except.ok result at success
            injection success with resultEq
            subst result
            have unifiedEq := unify_resolve_eq expectedResult
            have calleeInference :
                calleeRecord.2.inference = fittedState.inference := by
              simpa only [calleeRecord, allocation, recordExpression,
                State.recordNode] using
                  (allocateExpressionId_inference fittedState)
            have recordedEq :
                calleeRecord.2.resolve function.returnType =
                  calleeRecord.2.resolve expected := by
              unfold State.resolve
              rw [calleeInference]
              exact unifiedEq
            change outer.apply
                (calleeRecord.2.resolve function.returnType) =
              outer.apply expected
            calc
              outer.apply (calleeRecord.2.resolve function.returnType) =
                  outer.apply (calleeRecord.2.resolve expected) :=
                congrArg outer.apply recordedEq
              _ = outer.apply expected := by
                have applied := extension expected
                simpa only [callRecord, recordExpression, State.recordNode,
                  State.resolve, TypeSystem.InferState.resolve] using applied
  · simp [arity, bind, Except.bind] at success

/-- Recording an indirect call changes only typed-source metadata, so it
preserves readiness and the allocator bound already established for the
application result. -/
theorem recordIndirectCall_inferenceProperties
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult)
    (ready : result.state.InferenceReady)
    (resultBelow : result.result.type.VariablesBelow
      result.state.inference.next) :
    result.state.InferenceProgress
        (recordIndirectCall source callee arguments result).2 ∧
      (recordIndirectCall source callee arguments result).2.InferenceReady ∧
      (recordIndirectCall source callee arguments result).1.type.VariablesBelow
        (recordIndirectCall source callee arguments result).2.inference.next := by
  let recorded := recordIndirectCall source callee arguments result
  have progress : result.state.InferenceProgress recorded.2 := by
    apply State.InferenceProgress.of_inference_eq ready.solved
    rfl
  have recordedReady : recorded.2.InferenceReady :=
    State.InferenceReady.of_progress_of_binderEnvironment_eq ready progress rfl
  have returnedBelow : recorded.1.type.VariablesBelow
      recorded.2.inference.next := by
    simpa only [recorded, recordIndirectCall, recordExpression] using
      resultBelow.weaken progress.next_le
  change result.state.InferenceProgress recorded.2 ∧
    recorded.2.InferenceReady ∧
    recorded.1.type.VariablesBelow recorded.2.inference.next
  exact ⟨progress, recordedReady, returnedBelow⟩

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

private theorem applyFunctionType_lexicalScope
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.lexicalScope = state.lexicalScope := by
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
              exact (withExpected_lexicalScope resultResult).trans
                (withExpected_lexicalScope argumentResult)
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
              exact (withExpected_lexicalScope resultResult).trans
                ((unify_preserves_lexicalScope unifyResult).trans
                  (state_fresh_success_lexicalScope freshResultEq))

private theorem applyFunctionType_nextLocal
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.nextLocal = state.nextLocal := by
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
              exact (withExpected_nextLocal resultResult).trans
                (withExpected_nextLocal argumentResult)
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
              exact (withExpected_nextLocal resultResult).trans
                ((unify_preserves_nextLocal unifyResult).trans
                  (state_fresh_success_nextLocal freshResultEq))

@[simp] private theorem recordIndirectCall_state_header
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.header =
    result.state.header := by
  simp [recordIndirectCall]

@[simp] private theorem recordIndirectCall_lexicalScope
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.lexicalScope =
      result.state.lexicalScope := by
  simp [recordIndirectCall]

@[simp] private theorem recordIndirectCall_nextLocal
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.nextLocal =
      result.state.nextLocal := by
  simp [recordIndirectCall]

@[simp] private theorem recordIndirectCall_resolve
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult)
    (type : Ty) :
    (recordIndirectCall source callee arguments result).2.resolve type =
      result.state.resolve type := by
  simp only [recordIndirectCall, recordExpression, State.recordNode,
    State.resolve, TypeSystem.InferState.resolve]

@[simp] private theorem recordIndirectCall_inference
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression)
    (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.inference =
      result.state.inference := by
  simp only [recordIndirectCall, recordExpression, State.recordNode]

/-- Recording an indirect application leaves its already fitted result type
and inference substitution unchanged. -/
private theorem recordIndirectCall_application_apply_eq
    {context : Context} {source : Syntax.Expr}
    {callee : InferredExpression} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Ty} {state : State}
    {application : IndirectApplicationResult} {outer : Substitution}
    (applicationSuccess : applyFunctionType context call callee.type arguments
      (some expected) state = .ok application)
    (extension : outer.SemanticallyExtends
      (recordIndirectCall source callee arguments application).2.inference.substitution) :
    outer.apply
        (recordIndirectCall source callee arguments application).1.type =
      outer.apply expected := by
  have applicationExtension : outer.SemanticallyExtends
      application.state.inference.substitution := by
    simpa only [recordIndirectCall_inference] using extension
  change outer.apply application.result.type = outer.apply expected
  exact applyFunctionType_some_apply_eq applicationSuccess
    applicationExtension

/-- Constructor application performs a final ordinary expected-type record
after checking all payloads, so its returned type has the same coherence
property as that record. -/
private theorem inferConstructorApplicationFuel_some_apply_eq
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Ty} {state : State}
    {result : InferredExpression × State} {outer : Substitution}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments (some expected) state = .ok result)
    (extension : outer.SemanticallyExtends
      result.2.inference.substitution) :
    outer.apply result.1.type = outer.apply expected := by
  unfold inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity, if_false, bind, Except.bind] at success
    cases fittedResult : unify state instantiation.resultType expected with
    | error error =>
        simp [fittedResult, bind, Except.bind] at success
    | ok fittedState =>
        simp only [fittedResult, bind, Except.bind] at success
        cases argumentsResult : inferConstructorArgumentsFuel fuel context
            arguments instantiation.payloadTypes fittedState with
        | error error =>
            simp [argumentsResult, bind, Except.bind] at success
        | ok argumentsPair =>
            rcases argumentsPair with ⟨inferredArguments, argumentsState⟩
            simp only [argumentsResult, bind, Except.bind, Prod.eta] at success
            exact recordExpressionWithExpected_some_apply_eq success extension
  · simp [arity, bind, Except.bind] at success

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

private theorem unifyBuiltinFunctionArgumentsEqual_lexicalScope
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.lexicalScope = state.lexicalScope := by
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
              exact (induction success).trans
                (unify_preserves_lexicalScope unifyResult)

private theorem unifyBuiltinFunctionArgumentsEqual_nextLocal
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.nextLocal = state.nextLocal := by
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
              exact (induction success).trans
                (unify_preserves_nextLocal unifyResult)

private theorem functionCandidates_scheme_body_variablesBelow
    {context : Context} {candidates : List ProgramFunctionSignature}
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (subset : candidates ⊆ context.signatures.functions)
    (next : Nat) :
    ∀ signature ∈ candidates,
      signature.scheme.body.VariablesBelow next := by
  intro signature member
  have catalogMember := subset member
  exact validated.function_scheme_body_variablesBelow catalogMember
    (canonical signature catalogMember) next

private theorem generalizeValue_allocateBinder_inferenceProperties
    {state : State} {requirementStart : Nat} {valueType : Ty}
    {name : String} {span : Option Syntax.SourceSpan}
    (ready : state.InferenceReady)
    (valueTypeBelow : valueType.VariablesBelow state.inference.next) :
    let locals :=
      state.binderEnvironment.apply state.inference.substitution
    let resolvedType := state.resolve valueType
    let generalized :=
      generalizeValue state locals requirementStart resolvedType
    let result :=
      (state.withLocals locals).allocateBinder name generalized.scheme span
        false generalized.requirements
    state.InferenceProgress result.2 ∧ result.2.InferenceReady := by
  let locals :=
    state.binderEnvironment.apply state.inference.substitution
  let resolvedType := state.resolve valueType
  let generalized :=
    generalizeValue state locals requirementStart resolvedType
  let localState := state.withLocals locals
  let result := localState.allocateBinder name generalized.scheme span false
    generalized.requirements
  change state.InferenceProgress result.2 ∧ result.2.InferenceReady
  have resolvedTypeBelow :
      resolvedType.VariablesBelow state.inference.next := by
    change (state.inference.substitution.apply valueType).VariablesBelow
      state.inference.next
    exact ready.solved.variablesBelow_apply valueTypeBelow
  have generalizedBodyBelow :
      generalized.scheme.body.VariablesBelow state.inference.next := by
    simpa only [generalized, generalizeValue_scheme_body] using
      resolvedTypeBelow
  have localProgress : state.InferenceProgress localState := by
    simpa only [localState] using
      State.InferenceProgress.withLocals state locals ready.solved
  have localReady : localState.InferenceReady := by
    simpa only [localState] using State.InferenceReady.withLocals locals ready
  have bodyAtLocal :
      generalized.scheme.body.VariablesBelow localState.inference.next := by
    simpa only [localState, State.withLocals] using generalizedBodyBelow
  have allocationProgress : localState.InferenceProgress result.2 := by
    simpa only [result] using
      State.InferenceProgress.allocateBinder localState name
        generalized.scheme span false generalized.requirements
        localReady.solved
  have resultReady : result.2.InferenceReady := by
    simpa only [result] using
      State.InferenceReady.allocateBinder name generalized.scheme span false
        generalized.requirements localReady bodyAtLocal
  exact ⟨localProgress.trans allocationProgress, resultReady⟩

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

private theorem recordBuiltinFunctionCall_lexicalScope
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.lexicalScope = state.lexicalScope := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentsScope :=
    unifyBuiltinFunctionArgumentsEqual_lexicalScope (by assumption)
  all_goals try have unifiedScope :=
    unify_preserves_lexicalScope (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.lexicalScope, State.allocateExpressionId,
    State.recordNode, recordExpression, bind, Except.bind]

private theorem recordBuiltinFunctionCall_nextLocal
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.nextLocal = state.nextLocal := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentsNext :=
    unifyBuiltinFunctionArgumentsEqual_nextLocal (by assumption)
  all_goals try have unifiedNext :=
    unify_preserves_nextLocal (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.allocateExpressionId,
    State.recordNode, recordExpression, bind, Except.bind]

private theorem syntheticTuple_result_inferenceProperties
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (elementsBelow : ∀ element ∈ elements,
      element.type.VariablesBelow state.inference.next)
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
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
  have elementTypesBelow : ∀ type ∈ elements.map (·.type),
      type.VariablesBelow state.inference.next := by
    intro type member
    rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
    exact elementsBelow element elementMember
  have tupleTypeBelow :
      (Ty.productMany (elements.map (·.type))).VariablesBelow
        state.inference.next :=
    Ty.variablesBelow_productMany elementTypesBelow
  have allocationProgress :=
    State.InferenceProgress.allocateExpressionId state ready.solved
  have allocationReady := State.InferenceReady.allocateExpressionId ready
  have recordProgress := State.InferenceProgress.recordNode
    state.allocateExpressionId.snd (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    }) allocationReady.solved
  have recordReady := State.InferenceReady.recordNode (.expression {
    id := state.allocateExpressionId.fst
    span
    type := Ty.productMany (elements.map (·.type))
    form := .tuple (elements.map (·.id))
  }) allocationReady
  have progress := allocationProgress.trans recordProgress
  exact ⟨progress, recordReady, tupleTypeBelow.weaken progress.next_le⟩

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

private theorem allocateExpressionId_eq_inferenceProperties
    {initial next : State} {id : ExpressionId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateExpressionId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress :=
    State.InferenceProgress.allocateExpressionId initial ready.solved
  have nextReady := State.InferenceReady.allocateExpressionId ready
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

private theorem allocateStatementId_eq_inferenceProperties
    {initial next : State} {id : StatementId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateStatementId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress :=
    State.InferenceProgress.allocateStatementId initial ready.solved
  have nextReady := State.InferenceReady.allocateStatementId ready
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

/-- An explicitly named fresh allocation advances inference, preserves
readiness, and returns a metavariable below the advanced allocator. -/
theorem fresh_eq_inferenceProperties
    {initial next : State} {type : Ty}
    (ready : initial.InferenceReady)
    (allocation : initial.fresh = (type, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady ∧
      type.VariablesBelow next.inference.next := by
  have progress := State.InferenceProgress.fresh initial ready.solved
  have nextReady := State.InferenceReady.fresh ready
  have below : initial.fresh.1.VariablesBelow
      initial.fresh.2.inference.next := by
    change Ty.VariablesBelow (initial.inference.next + 1)
      (.variable ⟨initial.inference.next⟩)
    exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
  rw [allocation] at progress nextReady below
  exact ⟨progress, nextReady, below⟩

private def InferExprFuelExpectedTypeCoherent
    (fuel : Nat) (context : Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  ∀ expectedType, expected = some expectedType →
    ∀ result (outer : Substitution),
      inferExprFuel fuel context expression expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      outer.apply result.1.type = outer.apply expectedType

private def InferConstructorApplicationFuelExpectedTypeCoherent
    (fuel : Nat) (context : Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  ∀ expectedType, expected = some expectedType →
    ∀ result (outer : Substitution),
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      outer.SemanticallyExtends result.2.inference.substitution →
      outer.apply result.1.type = outer.apply expectedType

set_option maxHeartbeats 1000000 in
private theorem inferFuel_expectedTypeCoherent_internal :
    (∀ fuel context expression expected state,
      InferExprFuelExpectedTypeCoherent fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelExpectedTypeCoherent fuel context source id
        instantiation arguments expected state) ∧
    (∀ (_fuel : Nat) (_context : Context) (_sources : List Syntax.Expr)
      (_expected : List Ty) (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context)
      (_statements : List Syntax.Statement) (_expectedReturn : Ty)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_statement : Syntax.Statement)
      (_expectedReturn : Ty) (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_items : List Syntax.ForItem)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_item : Syntax.ForItem)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_target : Syntax.Expr)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_target : Syntax.Expr)
      (_operator : Syntax.ValueAssignOp) (_value : Syntax.Expr)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_expressions : List Syntax.Expr)
      (_state : State), True) ∧
    ∀ (_fuel : Nat) (_context : Context) (_scrutineeType : Ty)
      (_expectedReturn : Ty) (_outerScope : LexicalScope)
      (_cases : List Syntax.MatchCase) (_state : State), True := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelExpectedTypeCoherent)
    (motive2 := InferConstructorApplicationFuelExpectedTypeCoherent)
    (motive3 := fun _ _ _ _ _ => True)
    (motive4 := fun _ _ _ _ _ => True)
    (motive5 := fun _ _ _ _ _ => True)
    (motive6 := fun _ _ _ _ => True)
    (motive7 := fun _ _ _ _ => True)
    (motive8 := fun _ _ _ _ => True)
    (motive9 := fun _ _ _ _ _ _ => True)
    (motive10 := fun _ _ _ _ => True)
    (motive11 := fun _ _ _ _ _ _ _ => True)
  all_goals
    intros
    try trivial
  all_goals first
    | unfold InferConstructorApplicationFuelExpectedTypeCoherent
      intro expectedType expectedEq result outer success extension
      subst_vars
      exact inferConstructorApplicationFuel_some_apply_eq success extension
    | unfold InferExprFuelExpectedTypeCoherent at *
      intro expectedType expectedEq result outer success extension
      subst_vars
      unfold inferExprFuel at success
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
        | exact recordExpressionWithExpected_some_apply_eq
            (by assumption) extension
        | exact inferConstructorApplicationFuel_some_apply_eq
            (by assumption) extension
        | exact recordSelectedCall_selected_apply_eq (by assumption) extension
        | exact recordSelectedCallResult_withExpected_apply_eq
            (by assumption) extension
        | exact recordBuiltinFunctionCall_some_apply_eq
            (by assumption) extension
        | exact recordIndirectCall_application_apply_eq
            (by assumption) extension
        | simp_all [recordSelectedCall, recordSelectedCallResult,
            recordIndirectCall, recordExpression]

/-- Successful expression inference against a concrete expectation returns a
type equal to that expectation under every semantic extension of the final
inference substitution. -/
theorem inferExprFuel_expected_type_apply_eq
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Ty} {state : State} {result : InferredExpression × State}
    {outer : Substitution}
    (success : inferExprFuel fuel context expression (some expected) state =
      .ok result)
    (extension : outer.SemanticallyExtends
      result.2.inference.substitution) :
    outer.apply result.1.type = outer.apply expected := by
  exact inferFuel_expectedTypeCoherent_internal.1 fuel context expression
    (some expected) state expected rfl result outer success extension

private def FunctionSchemesCanonical (context : Context) : Prop :=
  ∀ signature ∈ context.signatures.functions,
    signature.scheme.body = .function
      (Ty.productMany signature.parameterTypes)
      (Ty.productMany signature.returnTypes)

private def InferExprFuelInferenceProperties
    (fuel : Nat) (context : Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      state.InferenceProgress result.2 ∧
        result.2.InferenceReady ∧
        result.1.type.VariablesBelow result.2.inference.next

private def InferConstructorApplicationFuelInferenceProperties
    (fuel : Nat) (context : Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    instantiation.resultType.VariablesBelow state.inference.next →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      state.InferenceProgress result.2 ∧
        result.2.InferenceReady ∧
        result.1.type.VariablesBelow result.2.inference.next

private def InferConstructorArgumentsFuelInferenceProperties
    (fuel : Nat) (context : Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      state.InferenceProgress result.2 ∧
        result.2.InferenceReady ∧
        ∀ expression ∈ result.1,
          expression.type.VariablesBelow result.2.inference.next

private def InferStatementsFuelInferenceProperties
    (fuel : Nat) (context : Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    expectedReturn.VariablesBelow state.inference.next →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      state.InferenceProgress result.state ∧
        result.state.InferenceReady ∧
        result.type.VariablesBelow result.state.inference.next

private def InferStatementFuelInferenceProperties
    (fuel : Nat) (context : Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    expectedReturn.VariablesBelow state.inference.next →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      state.InferenceProgress result.state ∧
        result.state.InferenceReady ∧
        result.type.VariablesBelow result.state.inference.next

private def InferForItemsFuelInferenceProperties
    (fuel : Nat) (context : Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      state.InferenceProgress result.state ∧ result.state.InferenceReady

private def InferForItemFuelInferenceProperties
    (fuel : Nat) (context : Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      state.InferenceProgress result.2 ∧ result.2.InferenceReady

private def InferPlaceFuelInferenceProperties
    (fuel : Nat) (context : Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      state.InferenceProgress result.2 ∧
        result.2.InferenceReady ∧
        result.1.type.VariablesBelow result.2.inference.next

private def InferAssignedValueFuelInferenceProperties
    (fuel : Nat) (context : Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      state.InferenceProgress result.2.2 ∧
        result.2.2.InferenceReady ∧
        result.1.target.type.VariablesBelow result.2.2.inference.next ∧
        result.2.1.type.VariablesBelow result.2.2.inference.next

private def InferExprsFuelInferenceProperties
    (fuel : Nat) (context : Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      state.InferenceProgress result.2 ∧
        result.2.InferenceReady ∧
        ∀ expression ∈ result.1,
          expression.type.VariablesBelow result.2.inference.next

private def InferMatchCasesFuelInferenceProperties
    (fuel : Nat) (context : Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    ProgramSignatureFormationValidated context.signatures →
    FunctionSchemesCanonical context →
    scrutineeType.VariablesBelow state.inference.next →
    expectedReturn.VariablesBelow state.inference.next →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      state.InferenceProgress result.state ∧
        result.state.InferenceReady ∧
        result.state.lexicalScope = outerScope

set_option maxHeartbeats 2000000 in
private theorem inferFuel_inferenceProperties_internal :
    (∀ fuel context expression expected state,
      InferExprFuelInferenceProperties fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelInferenceProperties fuel context source id
        instantiation arguments expected state) ∧
    (∀ fuel context sources expected state,
      InferConstructorArgumentsFuelInferenceProperties fuel context sources
        expected state) ∧
    (∀ fuel context statements expectedReturn state,
      InferStatementsFuelInferenceProperties fuel context statements
        expectedReturn state) ∧
    (∀ fuel context statement expectedReturn state,
      InferStatementFuelInferenceProperties fuel context statement
        expectedReturn state) ∧
    (∀ fuel context items state,
      InferForItemsFuelInferenceProperties fuel context items state) ∧
    (∀ fuel context item state,
      InferForItemFuelInferenceProperties fuel context item state) ∧
    (∀ fuel context target state,
      InferPlaceFuelInferenceProperties fuel context target state) ∧
    (∀ fuel context target operator value state,
      InferAssignedValueFuelInferenceProperties fuel context target operator
        value state) ∧
    (∀ fuel context expressions state,
      InferExprsFuelInferenceProperties fuel context expressions state) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelInferenceProperties fuel context scrutineeType
        expectedReturn outerScope cases state) := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelInferenceProperties)
    (motive2 := InferConstructorApplicationFuelInferenceProperties)
    (motive3 := InferConstructorArgumentsFuelInferenceProperties)
    (motive4 := InferStatementsFuelInferenceProperties)
    (motive5 := InferStatementFuelInferenceProperties)
    (motive6 := InferForItemsFuelInferenceProperties)
    (motive7 := InferForItemFuelInferenceProperties)
    (motive8 := InferPlaceFuelInferenceProperties)
    (motive9 := InferAssignedValueFuelInferenceProperties)
    (motive10 := InferExprsFuelInferenceProperties)
    (motive11 := InferMatchCasesFuelInferenceProperties)
  case case1 =>
    simp [InferExprFuelInferenceProperties, inferExprFuel]
  case case2 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelInferenceProperties
    intro ready _ _ expectedBelow result success
    let type : Ty := allocated.fresh.1
    let freshState : State := allocated.fresh.2
    let metavariable : TypeVarId := ⟨allocated.inference.next⟩
    let addition := freshState.addRequirementWithId
      (ProgramSignatures.builtinIntPredicate type)
    let literalState : State := {
      addition.2 with integerLiterals := addition.2.integerLiterals ++ [{
        metavariable
        expression := id
        requirement := addition.1
      }]
    }
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have freshProgress : allocated.InferenceProgress freshState := by
      simpa only [freshState] using
        State.InferenceProgress.fresh allocated allocatedReady.solved
    have freshReady : freshState.InferenceReady := by
      simpa only [freshState] using State.InferenceReady.fresh allocatedReady
    have typeBelowFresh : type.VariablesBelow
        freshState.inference.next := by
      change Ty.VariablesBelow (allocated.inference.next + 1)
        (.variable ⟨allocated.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
    have additionProgress : freshState.InferenceProgress addition.2 := by
      simpa only [addition] using
        State.InferenceProgress.addRequirementWithId freshState
          (ProgramSignatures.builtinIntPredicate type) freshReady.solved
    have additionReady : addition.2.InferenceReady := by
      simpa only [addition] using
        State.InferenceReady.addRequirementWithId
          (ProgramSignatures.builtinIntPredicate type) freshReady
    have metadataProgress : addition.2.InferenceProgress literalState := by
      exact State.InferenceProgress.of_inference_eq additionReady.solved rfl
    have metadataReady : literalState.InferenceReady :=
      State.InferenceReady.of_progress_of_binderEnvironment_eq additionReady
        metadataProgress rfl
    have prefixProgress : initial.InferenceProgress literalState :=
      allocationProgress.trans
        (freshProgress.trans (additionProgress.trans metadataProgress))
    have typeAtLiteral : type.VariablesBelow
        literalState.inference.next :=
      typeBelowFresh.weaken
        (additionProgress.trans metadataProgress).next_le
    have expectedAtLiteral : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow literalState.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken prefixProgress.next_le
    have recordSuccess :
        recordExpressionWithExpected context expression id type
          (.integerLiteral (.decimal spelling) {
            rawValue
            targetType := type
            requirement := addition.1
          }) [addition.1] expected literalState = .ok result := by
      unfold inferExprFuel at success
      simp only [allocationEq, expressionEq, literalEq, numericEq, bind,
        Except.bind, pure, Pure.pure, Except.pure] at success
      simpa only [type, freshState, metavariable, addition, literalState,
        State.fresh, TypeSystem.InferState.fresh, Prod.eta] using success
    have recordedProperties :=
      recordExpressionWithExpected_inferenceProperties metadataReady
        typeAtLiteral expectedAtLiteral recordSuccess
    exact ⟨prefixProgress.trans recordedProperties.1,
      recordedProperties.2⟩
  case case3 =>
    simp_all [InferExprFuelInferenceProperties, inferExprFuel, bind,
      Except.bind]
  case case4 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelInferenceProperties
    intro ready _ _ expectedBelow result success
    let type : Ty := allocated.fresh.1
    let freshState : State := allocated.fresh.2
    let metavariable : TypeVarId := ⟨allocated.inference.next⟩
    let addition := freshState.addRequirementWithId
      (ProgramSignatures.builtinIntPredicate type)
    let literalState : State := {
      addition.2 with integerLiterals := addition.2.integerLiterals ++ [{
        metavariable
        expression := id
        requirement := addition.1
      }]
    }
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have freshProgress : allocated.InferenceProgress freshState := by
      simpa only [freshState] using
        State.InferenceProgress.fresh allocated allocatedReady.solved
    have freshReady : freshState.InferenceReady := by
      simpa only [freshState] using State.InferenceReady.fresh allocatedReady
    have typeBelowFresh : type.VariablesBelow
        freshState.inference.next := by
      change Ty.VariablesBelow (allocated.inference.next + 1)
        (.variable ⟨allocated.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
    have additionProgress : freshState.InferenceProgress addition.2 := by
      simpa only [addition] using
        State.InferenceProgress.addRequirementWithId freshState
          (ProgramSignatures.builtinIntPredicate type) freshReady.solved
    have additionReady : addition.2.InferenceReady := by
      simpa only [addition] using
        State.InferenceReady.addRequirementWithId
          (ProgramSignatures.builtinIntPredicate type) freshReady
    have metadataProgress : addition.2.InferenceProgress literalState := by
      exact State.InferenceProgress.of_inference_eq additionReady.solved rfl
    have metadataReady : literalState.InferenceReady :=
      State.InferenceReady.of_progress_of_binderEnvironment_eq additionReady
        metadataProgress rfl
    have prefixProgress : initial.InferenceProgress literalState :=
      allocationProgress.trans
        (freshProgress.trans (additionProgress.trans metadataProgress))
    have typeAtLiteral : type.VariablesBelow
        literalState.inference.next :=
      typeBelowFresh.weaken
        (additionProgress.trans metadataProgress).next_le
    have expectedAtLiteral : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow literalState.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken prefixProgress.next_le
    have recordSuccess :
        recordExpressionWithExpected context expression id type
          (.integerLiteral (.hexadecimal spelling) {
            rawValue
            targetType := type
            requirement := addition.1
          }) [addition.1] expected literalState = .ok result := by
      unfold inferExprFuel at success
      simp only [allocationEq, expressionEq, literalEq, numericEq, bind,
        Except.bind, pure, Pure.pure, Except.pure] at success
      simpa only [type, freshState, metavariable, addition, literalState,
        State.fresh, TypeSystem.InferState.fresh, Prod.eta] using success
    have recordedProperties :=
      recordExpressionWithExpected_inferenceProperties metadataReady
        typeAtLiteral expectedAtLiteral recordSuccess
    exact ⟨prefixProgress.trans recordedProperties.1,
      recordedProperties.2⟩
  case case5 =>
    simp_all [InferExprFuelInferenceProperties, inferExprFuel, bind,
      Except.bind]
  case case6 =>
    simp_all [InferExprFuelInferenceProperties, inferExprFuel]
  case case7 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq binder lookupEq localSchemeInstantiationStart
      instantiated inference advanced predicates requirements recorded
      requirementsEq
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have instantiationProperties :=
      localBinderInstantiation_inferenceProperties allocatedReady lookupEq
    have instantiationProgress : allocated.InferenceProgress advanced := by
      simpa only [instantiated, inference, advanced] using
        instantiationProperties.1
    have advancedReady : advanced.InferenceReady := by
      simpa only [instantiated, inference, advanced] using
        instantiationProperties.2.1
    have bodyBelow :
        (advanced.resolve instantiated.body).VariablesBelow
          advanced.inference.next := by
      simpa only [instantiated, inference, advanced] using
        instantiationProperties.2.2
    have requirementsProgress : advanced.InferenceProgress recorded := by
      have progress := State.InferenceProgress.addRequirementsWithIds advanced
        predicates advancedReady.solved
      rw [requirementsEq] at progress
      exact progress
    have recordedReady : recorded.InferenceReady := by
      have nextReady :=
        State.InferenceReady.addRequirementsWithIds predicates advancedReady
      rw [requirementsEq] at nextReady
      exact nextReady
    have expectedAtRecorded : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow recorded.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        (allocationProgress.trans
          (instantiationProgress.trans requirementsProgress)).next_le
    have bodyAtRecorded :
        (advanced.resolve instantiated.body).VariablesBelow
          recorded.inference.next :=
      bodyBelow.weaken requirementsProgress.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupEq, requirementsEq, bind,
      Except.bind] at success
    have recordSuccess :
        recordExpressionWithExpected context expression id
          (advanced.resolve instantiated.body)
          (.reference name.value (.local binder.id)) requirements expected
          recorded (some localSchemeInstantiationStart) = .ok result := by
      simpa only [instantiated, inference, advanced, predicates,
        requirementsEq, localSchemeInstantiationStart] using success
    have recordedProperties :=
      recordExpressionWithExpected_inferenceProperties recordedReady
        bodyAtRecorded expectedAtRecorded recordSuccess
    exact ⟨allocationProgress.trans
        (instantiationProgress.trans
          (requirementsProgress.trans recordedProperties.1)),
      recordedProperties.2⟩
  case case8 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone isBoolean
    unfold InferExprFuelInferenceProperties
    intro ready _ _ expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, isBoolean, if_true]
      at success
    have recordedProperties :=
      recordExpressionWithExpected_inferenceProperties allocationProperties.2
        (Ty.variablesBelow_constructor _ _) expectedAtAllocated success
    exact ⟨allocationProperties.1.trans recordedProperties.1,
      recordedProperties.2⟩
  case case9 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone notBool
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProgress.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, notBool, bind,
      Except.bind] at success
    cases functionsResult : functionsNamed context name.value with
    | error error =>
        simp [functionsResult, bind, Except.bind] at success
    | ok candidates =>
        simp only [functionsResult, bind, Except.bind] at success
        cases candidates with
        | nil =>
            cases builtinResult : builtinFunctionNamed? name.value with
            | none => simp [builtinResult] at success
            | some function =>
                simp only [builtinResult] at success
                have recordedProperties :=
                  recordExpressionWithExpected_inferenceProperties
                    allocatedReady
                    (builtinFunction_type_variablesBelow function _)
                    expectedAtAllocated success
                exact ⟨allocationProgress.trans recordedProperties.1,
                  recordedProperties.2⟩
        | cons signature rest =>
            cases rest with
            | nil =>
                have catalogMember :
                    signature ∈ context.signatures.functions :=
                  functionsNamed_success_subset_catalog functionsResult
                    (by simp)
                have schemeBelow :=
                  validated.function_scheme_body_variablesBelow catalogMember
                    (canonical signature catalogMember)
                    allocated.inference.next
                have recordedProperties :=
                  recordInstantiatedFunctionReference_inferenceProperties
                    allocatedReady schemeBelow expectedAtAllocated success
                exact ⟨allocationProgress.trans recordedProperties.1,
                  recordedProperties.2⟩
            | cons second tail => simp at success
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases innerResult : inferExprFuel fuel context inner expected allocated with
    | error error =>
        simp [innerResult, bind, Except.bind] at success
    | ok innerPair =>
        rcases innerPair with ⟨inferred, innerState⟩
        simp only [innerResult, bind, Except.bind, Prod.eta] at success
        have innerProperties := innerInduction allocationProperties.2
          validated canonical
          (by
            intro expectedType member
            exact (expectedBelow expectedType member).weaken
              allocationProperties.1.next_le)
          (inferred, innerState) innerResult
        have prefixProgress := allocationProperties.1.trans innerProperties.1
        have recordedProperties :=
          recordExpressionWithExpected_inferenceProperties
            innerProperties.2.1 innerProperties.2.2
            (by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                prefixProgress.next_le)
            success
        exact ⟨prefixProgress.trans recordedProperties.1,
          recordedProperties.2⟩
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases elementsResult : inferExprsFuel fuel context elements.elements
        allocated with
    | error error =>
        simp [elementsResult, bind, Except.bind] at success
    | ok elementsPair =>
        rcases elementsPair with ⟨inferredElements, elementsState⟩
        simp only [elementsResult, bind, Except.bind, Prod.eta] at success
        have elementsProperties := elementsInduction allocationProperties.2
          validated canonical (inferredElements, elementsState) elementsResult
        have tupleTypeBelow :
            (Ty.productMany (inferredElements.map (·.type))).VariablesBelow
              elementsState.inference.next :=
          Ty.variablesBelow_productMany (by
            intro type member
            simp only [List.mem_map] at member
            obtain ⟨element, elementMember, rfl⟩ := member
            exact elementsProperties.2.2 element elementMember)
        have prefixProgress :=
          allocationProperties.1.trans elementsProperties.1
        have recordedProperties :=
          recordExpressionWithExpected_inferenceProperties
            elementsProperties.2.1 tupleTypeBelow
            (by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                prefixProgress.next_le)
            success
        exact ⟨prefixProgress.trans recordedProperties.1,
          recordedProperties.2⟩
  -- Unary operator expression, including overloaded dispatch.
  case case12 =>
    intros context expression expected initial fuel id allocated allocationEq
      operator operand expressionEq operandInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases operandResult : inferExprFuel fuel context operand none allocated with
    | error error =>
        simp [operandResult, bind, Except.bind] at success
    | ok operandPair =>
        rcases operandPair with ⟨inferredOperand, operandState⟩
        simp only [operandResult, bind, Except.bind, Prod.eta] at success
        have operandProperties := operandInduction allocationProperties.2
          validated canonical (by simp) (inferredOperand, operandState)
          operandResult
        have prefixProgress :=
          allocationProperties.1.trans operandProperties.1
        have expectedAtOperand : ∀ expectedType ∈ expected,
            expectedType.VariablesBelow operandState.inference.next := by
          intro expectedType member
          exact (expectedBelow expectedType member).weaken
            prefixProgress.next_le
        let integerLiterals := relevantIntegerLiterals operandState
          allocated.integerLiterals.length [inferredOperand]
        have finishInferred (inferred : OperatorInferenceResult)
            (inferenceSuccess : inferUnaryOperator context operator.value
              inferredOperand.type expected integerLiterals operandState =
                .ok inferred)
            (recordSuccess : recordExpressionWithExpected context expression id
              inferred.type (.unary operator.value inferredOperand.id)
              inferred.requirements expected inferred.state = .ok result) :
            initial.InferenceProgress result.2 ∧
              result.2.InferenceReady ∧
              result.1.type.VariablesBelow result.2.inference.next := by
          have inferredProperties := inferUnaryOperator_inferenceProperties
            operandProperties.2.1 operandProperties.2.2 expectedAtOperand
            inferenceSuccess
          have expectedAtInferred : ∀ expectedType ∈ expected,
              expectedType.VariablesBelow inferred.state.inference.next := by
            intro expectedType member
            exact (expectedAtOperand expectedType member).weaken
              inferredProperties.1.next_le
          have recordedProperties :=
            recordExpressionWithExpected_inferenceProperties
              inferredProperties.2.1 inferredProperties.2.2
              expectedAtInferred recordSuccess
          exact ⟨prefixProgress.trans
              (inferredProperties.1.trans recordedProperties.1),
            recordedProperties.2⟩
        cases dispatchEq : unaryOperatorDispatch operator.value with
        | traitMethod traitName methodName =>
            simp only [integerLiterals, dispatchEq] at success
            cases inferredResult : inferUnaryOperator context operator.value
                inferredOperand.type expected integerLiterals operandState with
            | error error =>
                simp [integerLiterals, inferredResult, bind, Except.bind]
                  at success
            | ok inferred =>
                simp only [integerLiterals, inferredResult, bind,
                  Except.bind] at success
                exact finishInferred inferred inferredResult success
        | function name =>
            simp only [integerLiterals, dispatchEq] at success
            cases functionsResult : functionsNamed context name with
            | error error =>
                simp [functionsResult, bind, Except.bind] at success
            | ok candidates =>
                simp only [functionsResult, bind, Except.bind] at success
                cases candidates with
                | nil =>
                    cases inferredResult : inferUnaryOperator context
                        operator.value inferredOperand.type expected
                        integerLiterals operandState with
                    | error error =>
                        simp [integerLiterals, inferredResult, bind,
                          Except.bind] at success
                    | ok inferred =>
                        simp only [integerLiterals, inferredResult, bind,
                          Except.bind] at success
                        exact finishInferred inferred inferredResult success
                | cons candidate rest =>
                    cases selectionResult : selectFunctionCandidateFrom context
                        name (candidate :: rest) [inferredOperand]
                        integerLiterals id expected operandState with
                    | error error =>
                        simp [integerLiterals, selectionResult, bind,
                          Except.bind] at success
                    | ok attempt =>
                        simp only [integerLiterals, selectionResult, bind,
                          Except.bind, pure, Pure.pure, Except.pure] at success
                        let callee : Syntax.Expr := {
                          span := operator.span
                          value := .identifier {
                            span := operator.span
                            value := name
                          }
                        }
                        change Except.ok (recordSelectedCall expression callee
                          name [inferredOperand] attempt) = Except.ok result
                            at success
                        injection success with resultEq
                        have selectedProperties :=
                          selectFunctionCandidateFrom_inferenceProperties
                            operandProperties.2.1
                            (by
                              intro argument member
                              simp only [List.mem_singleton] at member
                              subst argument
                              exact operandProperties.2.2)
                            (functionCandidates_scheme_body_variablesBelow
                              validated canonical
                              (functionsNamed_success_subset_catalog
                                functionsResult) _)
                            expectedAtOperand selectionResult
                        have recordedProperties :=
                          recordSelectedCall_inferenceProperties expression
                            callee name [inferredOperand] attempt
                            selectedProperties.2.1 selectedProperties.2.2
                        rw [← resultEq]
                        exact ⟨prefixProgress.trans
                            (selectedProperties.1.trans recordedProperties.1),
                          recordedProperties.2⟩
  -- Binary operator expression, including overloaded dispatch.
  case case13 =>
    intros context expression expected initial fuel id allocated allocationEq
      left operator right expressionEq leftInduction rightInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases leftResult : inferExprFuel fuel context left none allocated with
    | error error =>
        simp [leftResult, bind, Except.bind] at success
    | ok leftPair =>
        rcases leftPair with ⟨inferredLeft, leftState⟩
        simp only [leftResult, bind, Except.bind, Prod.eta] at success
        have leftProperties := leftInduction allocationProperties.2
          validated canonical (by simp) (inferredLeft, leftState) leftResult
        cases rightResult : inferExprFuel fuel context right none leftState with
        | error error =>
            simp [rightResult, bind, Except.bind] at success
        | ok rightPair =>
            rcases rightPair with ⟨inferredRight, rightState⟩
            simp only [rightResult, bind, Except.bind, Prod.eta] at success
            have rightProperties := rightInduction leftState
              leftProperties.2.1 validated canonical (by simp)
              (inferredRight, rightState) rightResult
            have leftAtRight : inferredLeft.type.VariablesBelow
                rightState.inference.next :=
              leftProperties.2.2.weaken rightProperties.1.next_le
            have argumentsBelow :
                ∀ argument ∈ [inferredLeft, inferredRight],
                  argument.type.VariablesBelow rightState.inference.next := by
              intro argument member
              simp only [List.mem_cons, List.mem_singleton] at member
              rcases member with rfl | member
              · exact leftAtRight
              · rcases member with rfl | member
                · exact rightProperties.2.2
                · simp at member
            have prefixProgress := allocationProperties.1.trans
              (leftProperties.1.trans rightProperties.1)
            have expectedAtRight : ∀ expectedType ∈ expected,
                expectedType.VariablesBelow rightState.inference.next := by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                prefixProgress.next_le
            let integerLiterals := relevantIntegerLiterals rightState
              allocated.integerLiterals.length [inferredLeft, inferredRight]
            have finishInferred (inferred : OperatorInferenceResult)
                (inferenceSuccess : inferBinaryOperator context operator.value
                  inferredLeft.type inferredRight.type expected integerLiterals
                    rightState = .ok inferred)
                (recordSuccess : recordExpressionWithExpected context
                  expression id inferred.type
                  (.binary inferredLeft.id operator.value inferredRight.id)
                  inferred.requirements expected inferred.state = .ok result) :
                initial.InferenceProgress result.2 ∧
                  result.2.InferenceReady ∧
                  result.1.type.VariablesBelow result.2.inference.next := by
              have inferredProperties :=
                inferBinaryOperator_inferenceProperties
                  rightProperties.2.1 leftAtRight rightProperties.2.2
                  expectedAtRight inferenceSuccess
              have expectedAtInferred : ∀ expectedType ∈ expected,
                  expectedType.VariablesBelow
                    inferred.state.inference.next := by
                intro expectedType member
                exact (expectedAtRight expectedType member).weaken
                  inferredProperties.1.next_le
              have recordedProperties :=
                recordExpressionWithExpected_inferenceProperties
                  inferredProperties.2.1 inferredProperties.2.2
                  expectedAtInferred recordSuccess
              exact ⟨prefixProgress.trans
                  (inferredProperties.1.trans recordedProperties.1),
                recordedProperties.2⟩
            cases dispatchEq : binaryOperatorDispatch operator.value with
            | traitMethod traitName methodName =>
                simp only [integerLiterals, dispatchEq] at success
                cases inferredResult : inferBinaryOperator context
                    operator.value inferredLeft.type inferredRight.type expected
                    integerLiterals rightState with
                | error error =>
                    simp [integerLiterals, inferredResult, bind, Except.bind]
                      at success
                | ok inferred =>
                    simp only [integerLiterals, inferredResult, bind,
                      Except.bind] at success
                    exact finishInferred inferred inferredResult success
            | function name =>
                simp only [integerLiterals, dispatchEq] at success
                cases functionsResult : functionsNamed context name with
                | error error =>
                    simp [functionsResult, bind, Except.bind] at success
                | ok candidates =>
                    simp only [functionsResult, bind, Except.bind] at success
                    cases candidates with
                    | nil =>
                        cases inferredResult : inferBinaryOperator context
                            operator.value inferredLeft.type inferredRight.type
                            expected integerLiterals rightState with
                        | error error =>
                            simp [integerLiterals, inferredResult, bind,
                              Except.bind] at success
                        | ok inferred =>
                            simp only [integerLiterals, inferredResult, bind,
                              Except.bind] at success
                            exact finishInferred inferred inferredResult success
                    | cons candidate rest =>
                        cases selectionResult : selectFunctionCandidateFrom
                            context name (candidate :: rest)
                            [inferredLeft, inferredRight] integerLiterals id
                            (some .bool) rightState with
                        | error error =>
                            simp [integerLiterals, selectionResult, bind,
                              Except.bind] at success
                        | ok attempt =>
                            simp only [integerLiterals, selectionResult, bind,
                              Except.bind] at success
                            have selectedProperties :=
                              selectFunctionCandidateFrom_inferenceProperties
                                rightProperties.2.1 argumentsBelow
                                (functionCandidates_scheme_body_variablesBelow
                                  validated canonical
                                  (functionsNamed_success_subset_catalog
                                    functionsResult) _)
                                (by
                                  intro expectedType member
                                  simp only [Option.mem_def] at member
                                  injection member with typeEq
                                  subst expectedType
                                  exact Ty.variablesBelow_constructor _ _)
                                selectionResult
                            have expectedAtAttempt :
                                ∀ expectedType ∈ expected,
                                  expectedType.VariablesBelow
                                    attempt.state.inference.next := by
                              intro expectedType member
                              exact (expectedAtRight expectedType member).weaken
                                selectedProperties.1.next_le
                            cases fittedResult : withExpected context
                                attempt.state attempt.result expected with
                            | error error =>
                                simp [fittedResult, bind, Except.bind]
                                  at success
                            | ok fitted =>
                                simp only [fittedResult, bind, Except.bind,
                                  pure, Pure.pure, Except.pure] at success
                                have fittedProperties :=
                                  withExpected_inferenceProperties
                                    selectedProperties.2.1
                                    selectedProperties.2.2 expectedAtAttempt
                                    fittedResult
                                let callee : Syntax.Expr := {
                                  span := operator.span
                                  value := .identifier {
                                    span := operator.span
                                    value := name
                                  }
                                }
                                change Except.ok
                                  (recordSelectedCallResult expression callee
                                    name [inferredLeft, inferredRight] attempt
                                    fitted.expression fitted.coercions
                                    fitted.state) = Except.ok result at success
                                injection success with resultEq
                                have recordedProperties :=
                                  recordSelectedCallResult_inferenceProperties
                                    expression callee name
                                    [inferredLeft, inferredRight] attempt
                                    fitted.expression fitted.coercions
                                    fitted.state fittedProperties.2.1
                                    fittedProperties.2.2
                                rw [← resultEq]
                                exact ⟨prefixProgress.trans
                                    (selectedProperties.1.trans
                                      (fittedProperties.1.trans
                                        recordedProperties.1)),
                                  recordedProperties.2⟩
  -- Conditional expression.
  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq
      conditionInduction thenInduction elseInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition
        (some .bool) allocated with
    | error error =>
        simp [conditionResult, bind, Except.bind] at success
    | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult, bind, Except.bind, Prod.eta] at success
        have conditionProperties := conditionInduction
          allocationProperties.2 validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact Ty.variablesBelow_constructor _ _)
          (inferredCondition, conditionState) conditionResult
        have throughCondition :=
          allocationProperties.1.trans conditionProperties.1
        have expectedAtCondition : ∀ expectedType ∈ expected,
            expectedType.VariablesBelow conditionState.inference.next := by
          intro expectedType member
          exact (expectedBelow expectedType member).weaken
            throughCondition.next_le
        cases thenResult : inferExprFuel fuel context thenBranch expected
            conditionState with
        | error error =>
            simp [thenResult, bind, Except.bind] at success
        | ok thenPair =>
            rcases thenPair with ⟨inferredThen, thenState⟩
            simp only [thenResult, bind, Except.bind, Prod.eta] at success
            have thenProperties := thenInduction conditionState
              conditionProperties.2.1 validated canonical expectedAtCondition
              (inferredThen, thenState) thenResult
            have throughThen := throughCondition.trans thenProperties.1
            have expectedAtThen : ∀ expectedType ∈ expected,
                expectedType.VariablesBelow thenState.inference.next := by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                throughThen.next_le
            cases elseResult : inferExprFuel fuel context elseBranch expected
                thenState with
            | error error =>
                simp [elseResult, bind, Except.bind] at success
            | ok elsePair =>
                rcases elsePair with ⟨inferredElse, elseState⟩
                simp only [elseResult, bind, Except.bind, Prod.eta] at success
                have elseProperties := elseInduction thenState
                  thenProperties.2.1 validated canonical expectedAtThen
                  (inferredElse, elseState) elseResult
                have thenAtElse : inferredThen.type.VariablesBelow
                    elseState.inference.next :=
                  thenProperties.2.2.weaken elseProperties.1.next_le
                cases unifyResult : unify elseState inferredThen.type
                    inferredElse.type with
                | error error =>
                    simp [unifyResult, bind, Except.bind] at success
                | ok unifiedState =>
                    simp only [unifyResult, bind, Except.bind] at success
                    have unifyProgress := unify_inferenceProgress
                      elseProperties.2.1.solved thenAtElse
                      elseProperties.2.2 unifyResult
                    have unifiedReady := unify_preserves_inferenceReady
                      elseProperties.2.1 thenAtElse elseProperties.2.2
                      unifyResult
                    have throughUnify := throughThen.trans
                      (elseProperties.1.trans unifyProgress)
                    have resolvedThenBelow :
                        (unifiedState.resolve inferredThen.type).VariablesBelow
                          unifiedState.inference.next :=
                      unifyProgress.resolve_variablesBelow thenAtElse
                    have expectedAtUnified : ∀ expectedType ∈ expected,
                        expectedType.VariablesBelow
                          unifiedState.inference.next := by
                      intro expectedType member
                      exact (expectedBelow expectedType member).weaken
                        throughUnify.next_le
                    have recordedProperties :=
                      recordExpressionWithExpected_inferenceProperties
                        unifiedReady resolvedThenBelow expectedAtUnified success
                    exact ⟨throughUnify.trans recordedProperties.1,
                      recordedProperties.2⟩
  case case19 =>
    intros context expression expected initial fuel id allocated allocationEq
      base brackets index expressionEq baseInduction indexInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases baseResult : inferExprFuel fuel context base none allocated with
    | error error =>
        simp [baseResult, bind, Except.bind] at success
    | ok basePair =>
        rcases basePair with ⟨inferredBase, baseState⟩
        simp only [baseResult, bind, Except.bind, Prod.eta] at success
        have baseProperties := baseInduction allocationProperties.2
          validated canonical (by simp) (inferredBase, baseState) baseResult
        let keyAllocation := baseState.fresh
        have keyProperties := fresh_eq_inferenceProperties
          baseProperties.2.1 (type := keyAllocation.1)
          (next := keyAllocation.2) rfl
        let valueAllocation := keyAllocation.2.fresh
        have valueProperties := fresh_eq_inferenceProperties
          keyProperties.2.1 (type := valueAllocation.1)
          (next := valueAllocation.2) rfl
        have baseAtValue : inferredBase.type.VariablesBelow
            valueAllocation.2.inference.next :=
          baseProperties.2.2.weaken
            (keyProperties.1.trans valueProperties.1).next_le
        have keyAtValue : keyAllocation.1.VariablesBelow
            valueAllocation.2.inference.next :=
          keyProperties.2.2.weaken valueProperties.1.next_le
        have mappingBelow :
            (Ty.mapping keyAllocation.1 valueAllocation.1).VariablesBelow
              valueAllocation.2.inference.next :=
          (Ty.variablesBelow_mapping_iff _ _ _).2
            ⟨keyAtValue, valueProperties.2.2⟩
        cases unifyResult : unify valueAllocation.2 inferredBase.type
            (.mapping keyAllocation.1 valueAllocation.1) with
        | error error =>
            simp [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
        | ok unifiedState =>
            simp only [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
            have unifyProgress := unify_inferenceProgress
              valueProperties.2.1.solved baseAtValue mappingBelow unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              valueProperties.2.1 baseAtValue mappingBelow unifyResult
            have keyAtUnified : keyAllocation.1.VariablesBelow
                unifiedState.inference.next :=
              keyAtValue.weaken unifyProgress.next_le
            have resolvedKeyBelow :
                (unifiedState.resolve keyAllocation.1).VariablesBelow
                  unifiedState.inference.next :=
              unifiedReady.solved.variablesBelow_apply keyAtUnified
            cases indexResult : inferExprFuel fuel context index
                (some (unifiedState.resolve baseState.fresh.1))
                unifiedState with
            | error error =>
                simp [indexResult, bind, Except.bind] at success
            | ok indexPair =>
                rcases indexPair with ⟨inferredIndex, indexState⟩
                simp only [indexResult, bind, Except.bind, Prod.eta]
                  at success
                have indexProperties := indexInduction baseState.fresh.1
                  unifiedState unifiedReady validated canonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    simpa only [keyAllocation] using resolvedKeyBelow)
                  (inferredIndex, indexState) indexResult
                have fromValueToIndex :=
                  unifyProgress.trans indexProperties.1
                have resolvedValueBelow :=
                  fromValueToIndex.resolve_variablesBelow
                    valueProperties.2.2
                have prefixProgress := allocationProperties.1.trans
                  (baseProperties.1.trans
                    (keyProperties.1.trans
                      (valueProperties.1.trans fromValueToIndex)))
                have expectedAtIndex : ∀ expectedType ∈ expected,
                    expectedType.VariablesBelow indexState.inference.next := by
                  intro expectedType member
                  exact (expectedBelow expectedType member).weaken
                    prefixProgress.next_le
                have recordedProperties :=
                  recordExpressionWithExpected_inferenceProperties
                    indexProperties.2.1 resolvedValueBelow expectedAtIndex
                    success
                exact ⟨prefixProgress.trans recordedProperties.1,
                  recordedProperties.2⟩
  case case21 =>
    simp_all [InferExprFuelInferenceProperties, inferExprFuel]
  case case22 =>
    simp_all [InferExprFuelInferenceProperties, inferExprFuel]
  case case17 =>
    intros context expression expected initial fuel id allocated allocationEq
      dot name arguments expressionEq constructorInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidateResult : contextualConstructorCandidate context allocated
        expected name.value with
    | error error =>
        simp [candidateResult, bind, Except.bind] at success
    | ok candidate =>
        rcases candidate with ⟨dataType, constructor, typeArguments⟩
        simp only [candidateResult, bind, Except.bind] at success
        have instantiationBelow :=
          contextualConstructorCandidate_success_instantiation_variablesBelow
            allocationProperties.2 expectedAtAllocated validated
            candidateResult
        have constructorProperties := constructorInduction dataType
          constructor typeArguments allocationProperties.2 validated canonical
          instantiationBelow.1 instantiationBelow.2 expectedAtAllocated result
          success
        exact ⟨allocationProperties.1.trans constructorProperties.1,
          constructorProperties.2⟩
  case case18 =>
    intros context expression expected initial fuel id allocated allocationEq
      marker sourceType expressionEq
    unfold InferExprFuelInferenceProperties
    intro ready _ _ expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult, bind, Except.bind] at success
    | ok inner =>
        simp only [sourceTypeResult, bind, Except.bind] at success
        have innerBelow :=
          resolveSourceType_success_variablesBelow sourceTypeResult
            allocated.inference.next
        have proxyBelow : (Ty.proxy inner).VariablesBelow
            allocated.inference.next :=
          (Ty.variablesBelow_proxy_iff _ _).2 innerBelow
        have recordedProperties :=
          recordExpressionWithExpected_inferenceProperties
            allocationProperties.2 proxyBelow expectedAtAllocated success
        exact ⟨allocationProperties.1.trans recordedProperties.1,
          recordedProperties.2⟩
  case case20 =>
    intros context expression expected initial fuel id allocated allocationEq
      base dot name expressionEq constructorInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidatesResult :
        constructorCalleeCandidates context allocated expression with
    | error error =>
        simp [candidatesResult, bind, Except.bind] at success
    | ok candidates =>
        simp only [candidatesResult, bind, Except.bind] at success
        cases candidates with
        | nil =>
            simp_all [bind, Except.bind]
            repeat' first | split at success
            all_goals contradiction
        | cons candidate rest =>
            cases rest with
            | cons second tail => simp at success
            | nil =>
                rcases candidate with ⟨dataType, constructor⟩
                let freshResult :=
                  freshDataConstructorInstantiation dataType constructor
                    allocated
                have candidateFacts :=
                  constructorCalleeCandidates_success_members candidatesResult
                    dataType constructor (by simp)
                have payloadTypesBelow :=
                  validated.data_constructor_payloadTypes_variablesBelow
                    candidateFacts.1 candidateFacts.2
                    allocated.inference.next
                have freshProperties :=
                  freshDataConstructorInstantiation_inferenceProperties
                    dataType constructor allocated allocationProperties.2
                    payloadTypesBelow
                have constructorProperties := constructorInduction
                  freshResult.1 freshResult.2 freshProperties.2.1 validated
                  canonical freshProperties.2.2.2.1 freshProperties.2.2.2.2
                  (by
                    intro expectedType member
                    exact (expectedAtAllocated expectedType member).weaken
                      freshProperties.1.next_le)
                  result
                  (by simpa only [freshResult] using success)
                exact ⟨allocationProperties.1.trans
                    (freshProperties.1.trans constructorProperties.1),
                  constructorProperties.2⟩
  case case23 =>
    intros fuel context source id instantiation arguments expected initial
      arityEq argumentsInduction
    unfold InferConstructorApplicationFuelInferenceProperties
    intro ready validated canonical payloadTypesBelow resultTypeBelow
      expectedBelow result success
    unfold inferConstructorApplicationFuel at success
    simp only [arityEq, if_false, bind, Except.bind] at success
    let fittedComputation : Except Error State :=
      match expected with
      | none => pure initial
      | some expectedType => unify initial instantiation.resultType expectedType
    have fittedProperties : ∀ fittedState,
        fittedComputation = .ok fittedState →
        initial.InferenceProgress fittedState ∧
          fittedState.InferenceReady := by
      intro fittedState fittedSuccess
      unfold fittedComputation at fittedSuccess
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure] at fittedSuccess
          injection fittedSuccess with stateEq
          subst fittedState
          exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
      | some expectedType =>
          exact ⟨unify_inferenceProgress ready.solved resultTypeBelow
              (expectedBelow expectedType (by simp)) fittedSuccess,
            unify_preserves_inferenceReady ready resultTypeBelow
              (expectedBelow expectedType (by simp)) fittedSuccess⟩
    cases expected with
    | none =>
        simp only [pure, Pure.pure, Except.pure] at success
        cases argumentsResult : inferConstructorArgumentsFuel fuel context
            arguments instantiation.payloadTypes initial with
        | error error =>
            simp [argumentsResult, bind, Except.bind] at success
        | ok argumentsPair =>
            rcases argumentsPair with ⟨inferredArguments, argumentsState⟩
            simp only [argumentsResult, bind, Except.bind, Prod.eta] at success
            have argumentsProperties := argumentsInduction initial ready
              validated canonical payloadTypesBelow
              (inferredArguments, argumentsState) argumentsResult
            have resultAtArguments :=
              argumentsProperties.1.resolve_variablesBelow resultTypeBelow
            have recordedProperties :=
              recordExpressionWithExpected_inferenceProperties
                argumentsProperties.2.1 resultAtArguments (by simp) success
            exact ⟨argumentsProperties.1.trans recordedProperties.1,
              recordedProperties.2⟩
    | some expectedType =>
        cases fittedResult : unify initial instantiation.resultType
            expectedType with
        | error error =>
            simp [fittedResult, bind, Except.bind] at success
        | ok fittedState =>
            simp only [fittedResult, bind, Except.bind] at success
            have fitProperties := fittedProperties fittedState (by
              simpa only [fittedComputation] using fittedResult)
            have payloadAtFitted : ∀ payload ∈ instantiation.payloadTypes,
                payload.VariablesBelow fittedState.inference.next := by
              intro payload member
              exact (payloadTypesBelow payload member).weaken
                fitProperties.1.next_le
            cases argumentsResult : inferConstructorArgumentsFuel fuel context
                arguments instantiation.payloadTypes fittedState with
            | error error =>
                simp [argumentsResult, bind, Except.bind] at success
            | ok argumentsPair =>
                rcases argumentsPair with
                  ⟨inferredArguments, argumentsState⟩
                simp only [argumentsResult, bind, Except.bind, Prod.eta]
                  at success
                have argumentsProperties := argumentsInduction fittedState
                  fitProperties.2 validated canonical payloadAtFitted
                  (inferredArguments, argumentsState) argumentsResult
                have throughArguments :=
                  fitProperties.1.trans argumentsProperties.1
                have resultAtArguments :=
                  throughArguments.resolve_variablesBelow resultTypeBelow
                have expectedAtArguments : ∀ candidate : Ty,
                    candidate ∈ some expectedType →
                    candidate.VariablesBelow
                      argumentsState.inference.next := by
                  intro candidate member
                  simp only [Option.mem_def] at member
                  injection member with typeEq
                  subst candidate
                  exact (expectedBelow expectedType (by simp)).weaken
                    throughArguments.next_le
                have recordedProperties :=
                  recordExpressionWithExpected_inferenceProperties
                    argumentsProperties.2.1 resultAtArguments
                    expectedAtArguments success
                exact ⟨throughArguments.trans recordedProperties.1,
                  recordedProperties.2⟩
  case case24 =>
    simp_all [InferConstructorApplicationFuelInferenceProperties,
      inferConstructorApplicationFuel, bind, Except.bind]
  case case25 =>
    intros fuel context initial
    unfold InferConstructorArgumentsFuelInferenceProperties
    intro ready _ _ _ result success
    unfold inferConstructorArgumentsFuel at success
    injection success with resultEq
    subst result
    exact ⟨State.InferenceProgress.refl ready.solved, ready, by simp⟩
  case case26 =>
    intros fuel context source sources expected expectedTypes initial
      sourceInduction tailInduction
    unfold InferConstructorArgumentsFuelInferenceProperties
    intro ready validated canonical expectedTypesBelow result success
    unfold inferConstructorArgumentsFuel at success
    cases sourceResult : inferExprFuel fuel context source
        (some (initial.resolve expected)) initial with
    | error error =>
        simp [sourceResult, bind, Except.bind] at success
    | ok sourcePair =>
        rcases sourcePair with ⟨inferred, sourceState⟩
        simp only [sourceResult, bind, Except.bind] at success
        cases tailResult : inferConstructorArgumentsFuel fuel context sources
            expectedTypes sourceState with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok tailPair =>
            rcases tailPair with ⟨tail, finalState⟩
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            have expectedBelow := expectedTypesBelow expected (by simp)
            have sourceProperties := sourceInduction ready validated canonical
              (by
                intro expectedType member
                simp at member
                subst expectedType
                exact ready.solved.variablesBelow_apply expectedBelow)
              (inferred, sourceState) sourceResult
            have tailExpectedBelow : ∀ expectedType ∈ expectedTypes,
                expectedType.VariablesBelow sourceState.inference.next := by
              intro expectedType member
              exact (expectedTypesBelow expectedType (by simp [member])).weaken
                sourceProperties.1.next_le
            have tailProperties := tailInduction sourceState
              sourceProperties.2.1 validated canonical tailExpectedBelow
              (tail, finalState) tailResult
            refine ⟨sourceProperties.1.trans tailProperties.1,
              tailProperties.2.1, ?_⟩
            intro expression member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact sourceProperties.2.2.weaken tailProperties.1.next_le
            · exact tailProperties.2.2 expression tailMember
  case case27 =>
    simp_all [InferConstructorArgumentsFuelInferenceProperties,
      inferConstructorArgumentsFuel]
  case case28 =>
    simp [InferStatementsFuelInferenceProperties, inferStatementsFuel]
  case case29 =>
    intros context expectedReturn initial fuel
    unfold InferStatementsFuelInferenceProperties
    intro ready _ _ _ result success
    unfold inferStatementsFuel at success
    injection success with resultEq
    subst result
    exact ⟨State.InferenceProgress.refl ready.solved, ready,
      Ty.variablesBelow_constructor _ _⟩
  case case30 =>
    intros context expectedReturn initial fuel statement rest
      statementInduction tailInduction
    unfold InferStatementsFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    unfold inferStatementsFuel at success
    cases headResult : inferStatementFuel fuel context statement expectedReturn
        initial with
    | error error =>
        simp [headResult, bind, Except.bind] at success
    | ok head =>
        simp only [headResult, bind, Except.bind] at success
        have headProperties := statementInduction ready validated canonical
          returnBelow head headResult
        cases rest with
        | nil =>
            injection success with resultEq
            rw [← resultEq]
            refine ⟨headProperties.1, headProperties.2.1, ?_⟩
            split
            · exact headProperties.2.2
            · exact Ty.variablesBelow_constructor _ _
        | cons next remaining =>
            cases tailResult : inferStatementsFuel fuel context
                (next :: remaining) expectedReturn head.state with
            | error error =>
                simp [tailResult, bind, Except.bind] at success
            | ok tail =>
                simp only [tailResult, bind, Except.bind] at success
                injection success with resultEq
                rw [← resultEq]
                have tailProperties := tailInduction head headProperties.2.1
                  validated canonical
                  (returnBelow.weaken headProperties.1.next_le) tail tailResult
                refine ⟨headProperties.1.trans tailProperties.1,
                  tailProperties.2.1, ?_⟩
                split
                · exact tailProperties.2.2
                · split
                  · exact headProperties.2.2.weaken
                      tailProperties.1.next_le
                  · exact tailProperties.2.2
  case case31 =>
    simp [InferStatementFuelInferenceProperties, inferStatementFuel]
  case case32 =>
    simp_all [InferStatementFuelInferenceProperties, inferStatementFuel,
      bind, Except.bind]
  case case33 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType statementEq
    unfold InferStatementFuelInferenceProperties
    intro ready _ _ _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult, bind, Except.bind] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, bind, Except.bind, pure, Pure.pure,
          Except.pure] at success
        let binding :=
          let locals := allocated.binderEnvironment.apply
            allocated.inference.substitution
          let valueType := allocated.resolve resolvedType
          let generalized := generalizeValue allocated locals
            allocated.nextRequirement valueType
          (allocated.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingProperties : allocated.InferenceProgress binding.2 ∧
            binding.2.InferenceReady := by
          simpa only [binding] using
            generalizeValue_allocateBinder_inferenceProperties
              (state := allocated)
              (requirementStart := allocated.nextRequirement)
              (valueType := resolvedType) (name := name.value)
              (span := some name.span) allocationProperties.2
              (resolveSourceType_success_variablesBelow sourceTypeResult _)
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationProperties.1.trans
            (bindingProperties.1.trans
              (State.InferenceProgress.recordNode _ _
                bindingProperties.2.solved)),
          State.InferenceReady.recordNode _ bindingProperties.2,
          Ty.variablesBelow_constructor _ _⟩
  case case34 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name initializer statementEq initializerInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none
        allocated with
    | error error =>
        simp [initializerResult, bind, Except.bind] at success
    | ok initializerPair =>
        rcases initializerPair with ⟨inferred, initializerState⟩
        simp only [initializerResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        have initializerProperties := initializerInduction
          allocationProperties.2 validated canonical (by simp)
          (inferred, initializerState) initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            allocated.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingProperties :
            initializerState.InferenceProgress binding.2 ∧
              binding.2.InferenceReady := by
          simpa only [binding] using
            generalizeValue_allocateBinder_inferenceProperties
              (state := initializerState)
              (requirementStart := allocated.nextRequirement)
              (valueType := inferred.type) (name := name.value)
              (span := some name.span) initializerProperties.2.1
              initializerProperties.2.2
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationProperties.1.trans
            (initializerProperties.1.trans
              (bindingProperties.1.trans
                (State.InferenceProgress.recordNode _ _
                  bindingProperties.2.solved))),
          State.InferenceReady.recordNode _ bindingProperties.2,
          Ty.variablesBelow_constructor _ _⟩
  case case35 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType initializer statementEq
      initializerInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult, bind, Except.bind] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, bind, Except.bind] at success
        have resolvedTypeBelow :
            resolvedType.VariablesBelow allocated.inference.next :=
          resolveSourceType_success_variablesBelow sourceTypeResult _
        cases initializerResult : inferExprFuel fuel context initializer
            (some resolvedType) allocated with
        | error error =>
            simp [initializerResult, bind, Except.bind] at success
        | ok initializerPair =>
            rcases initializerPair with ⟨inferred, initializerState⟩
            simp only [initializerResult, bind, Except.bind, Prod.eta, pure,
              Pure.pure, Except.pure] at success
            have initializerProperties := initializerInduction resolvedType
              allocationProperties.2 validated canonical
              (by
                intro expectedType member
                simp only [Option.mem_def] at member
                injection member with typeEq
                subst expectedType
                exact resolvedTypeBelow)
              (inferred, initializerState) initializerResult
            let binding :=
              let locals := initializerState.binderEnvironment.apply
                initializerState.inference.substitution
              let valueType := initializerState.resolve inferred.type
              let generalized := generalizeValue initializerState locals
                allocated.nextRequirement valueType
              (initializerState.withLocals locals).allocateBinder name.value
                generalized.scheme (some name.span) false
                generalized.requirements
            have bindingProperties :
                initializerState.InferenceProgress binding.2 ∧
                  binding.2.InferenceReady := by
              simpa only [binding] using
                generalizeValue_allocateBinder_inferenceProperties
                  (state := initializerState)
                  (requirementStart := allocated.nextRequirement)
                  (valueType := inferred.type) (name := name.value)
                  (span := some name.span) initializerProperties.2.1
                  initializerProperties.2.2
            injection success with resultEq
            rw [← resultEq]
            refine ⟨allocationProperties.1.trans
                (initializerProperties.1.trans
                  (bindingProperties.1.trans
                    (State.InferenceProgress.recordNode _ _
                      bindingProperties.2.solved))),
              State.InferenceReady.recordNode _ bindingProperties.2,
              Ty.variablesBelow_constructor _ _⟩
  case case36 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq
    unfold InferStatementFuelInferenceProperties
    intro ready _ _ returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases unifyResult : unify allocated .unit expectedReturn with
    | error error =>
        simp [unifyResult, bind, Except.bind] at success
    | ok unifiedState =>
        simp only [unifyResult, bind, Except.bind, pure, Pure.pure,
          Except.pure] at success
        have unifyProgress := unify_inferenceProgress
          allocationProperties.2.solved (Ty.variablesBelow_constructor _ _)
          returnAtAllocated unifyResult
        have unifiedReady := unify_preserves_inferenceReady
          allocationProperties.2 (Ty.variablesBelow_constructor _ _)
          returnAtAllocated unifyResult
        have throughUnify := allocationProperties.1.trans unifyProgress
        have resultTypeBelow :=
          throughUnify.resolve_variablesBelow returnBelow
        injection success with resultEq
        rw [← resultEq]
        refine ⟨throughUnify.trans
            (State.InferenceProgress.recordNode _ _ unifiedReady.solved),
          State.InferenceReady.recordNode _ unifiedReady, resultTypeBelow⟩
  case case37 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq value statementEq valueInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases valueResult : inferExprFuel fuel context value
        (some expectedReturn) allocated with
    | error error =>
        simp [valueResult, bind, Except.bind] at success
    | ok valuePair =>
        rcases valuePair with ⟨inferred, valueState⟩
        simp only [valueResult, bind, Except.bind, Prod.eta, pure, Pure.pure,
          Except.pure] at success
        have valueProperties := valueInduction allocationProperties.2
          validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact returnAtAllocated)
          (inferred, valueState) valueResult
        have prefixProgress :=
          allocationProperties.1.trans valueProperties.1
        have resultTypeBelow :=
          prefixProgress.resolve_variablesBelow returnBelow
        injection success with resultEq
        rw [← resultEq]
        refine ⟨prefixProgress.trans
            (State.InferenceProgress.recordNode _ _
              valueProperties.2.1.solved),
          State.InferenceReady.recordNode _ valueProperties.2.1,
          resultTypeBelow⟩
  case case38 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq expression trailingSemicolon statementEq
      expressionInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases expressionResult : inferExprFuel fuel context expression none
        allocated with
    | error error =>
        simp [expressionResult, bind, Except.bind] at success
    | ok expressionPair =>
        rcases expressionPair with ⟨inferred, expressionState⟩
        simp only [expressionResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        have expressionProperties := expressionInduction
          allocationProperties.2 validated canonical (by simp)
          (inferred, expressionState) expressionResult
        have prefixProgress :=
          allocationProperties.1.trans expressionProperties.1
        injection success with resultEq
        rw [← resultEq]
        refine ⟨prefixProgress.trans
            (State.InferenceProgress.recordNode _ _
              expressionProperties.2.1.solved),
          State.InferenceReady.recordNode _ expressionProperties.2.1, ?_⟩
        split
        · exact Ty.variablesBelow_constructor _ _
        · exact expressionProperties.2.2
  case case39 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition thenBody elseBody statementEq
      conditionInduction thenInduction elseInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition (some .bool)
        allocated with
    | error error =>
        simp [conditionResult, bind, Except.bind] at success
    | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult, bind, Except.bind, Prod.eta] at success
        have conditionProperties := conditionInduction allocationProperties.2
          validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact Ty.variablesBelow_constructor _ _)
          (inferredCondition, conditionState) conditionResult
        have throughCondition :=
          allocationProperties.1.trans conditionProperties.1
        cases thenResultEq : inferStatementsFuel fuel context thenBody.value
            expectedReturn conditionState with
        | error error =>
            simp [thenResultEq, bind, Except.bind] at success
        | ok thenResult =>
            simp only [thenResultEq, bind, Except.bind] at success
            have thenProperties := thenInduction conditionState
              conditionProperties.2.1 validated canonical
              (returnBelow.weaken throughCondition.next_le) thenResult
              thenResultEq
            let afterThen := thenResult.state.restoreLexicalScope
              conditionState.lexicalScope
            have restoredThen :
                conditionState.InferenceProgress afterThen ∧
                  afterThen.InferenceReady := by
              simpa only [afterThen] using
                State.restoreLexicalScope_inferenceProperties
                  conditionProperties.2.1 thenProperties.1
            cases elseBody with
            | none =>
                simp only [afterThen, pure, Pure.pure, Except.pure] at success
                injection success with resultEq
                rw [← resultEq]
                refine ⟨throughCondition.trans
                    (restoredThen.1.trans
                      (State.InferenceProgress.recordNode _ _
                        restoredThen.2.solved)),
                  State.InferenceReady.recordNode _ restoredThen.2,
                  Ty.variablesBelow_constructor _ _⟩
            | some elseBody =>
                cases elseResultEq : inferStatementsFuel fuel context
                    elseBody.value expectedReturn afterThen with
                | error error =>
                    simp [afterThen, elseResultEq, bind, Except.bind]
                      at success
                | ok elseResult =>
                    simp only [afterThen, elseResultEq, bind, Except.bind,
                      pure, Pure.pure, Except.pure] at success
                    have elseProperties := elseInduction conditionState
                      thenResult elseBody restoredThen.2 validated canonical
                      (returnBelow.weaken
                        (throughCondition.trans restoredThen.1).next_le)
                      elseResult elseResultEq
                    have restoredElse :=
                      State.restoreLexicalScope_inferenceProperties
                        conditionProperties.2.1
                        (restoredThen.1.trans elseProperties.1)
                    have throughElse :=
                      throughCondition.trans restoredElse.1
                    injection success with resultEq
                    rw [← resultEq]
                    refine ⟨throughElse.trans
                        (State.InferenceProgress.recordNode _ _
                          restoredElse.2.solved),
                      State.InferenceReady.recordNode _ restoredElse.2, ?_⟩
                    split
                    · exact throughElse.resolve_variablesBelow returnBelow
                    · exact Ty.variablesBelow_constructor _ _
  case case40 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq body statementEq bodyInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases bodyResultEq : inferStatementsFuel fuel context body expectedReturn
        allocated with
    | error error =>
        simp [bodyResultEq, bind, Except.bind] at success
    | ok bodyResult =>
        simp only [bodyResultEq, bind, Except.bind, pure, Pure.pure,
          Except.pure] at success
        have bodyProperties := bodyInduction allocationProperties.2 validated
          canonical (returnBelow.weaken allocationProperties.1.next_le)
          bodyResult bodyResultEq
        have restoredBody :=
          State.restoreLexicalScope_inferenceProperties allocationProperties.2
            bodyProperties.1
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationProperties.1.trans
            (restoredBody.1.trans
              (State.InferenceProgress.recordNode _ _
                restoredBody.2.solved)),
          State.InferenceReady.recordNode _ restoredBody.2,
          bodyProperties.2.2⟩
  case case41 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator value statementEq assignmentInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases assignmentResult : inferAssignedValueFuel fuel context target
        operator.value value allocated with
    | error error =>
        simp [assignmentResult, bind, Except.bind] at success
    | ok assignmentTriple =>
        rcases assignmentTriple with
          ⟨assignment, inferredValue, assignmentState⟩
        simp only [assignmentResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        have assignmentProperties := assignmentInduction
          allocationProperties.2 validated canonical
          (assignment, inferredValue, assignmentState) assignmentResult
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationProperties.1.trans
            (assignmentProperties.1.trans
              (State.InferenceProgress.recordNode _ _
                assignmentProperties.2.1.solved)),
          State.InferenceReady.recordNode _ assignmentProperties.2.1,
          Ty.variablesBelow_constructor _ _⟩
  case case42 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator statementEq placeInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases placeResult : inferPlaceFuel fuel context target allocated with
    | error error =>
        simp [placeResult, bind, Except.bind] at success
    | ok placePair =>
        rcases placePair with ⟨inferredTarget, placeState⟩
        simp only [placeResult, bind, Except.bind, Prod.eta] at success
        have placeProperties := placeInduction allocationProperties.2
          validated canonical (inferredTarget, placeState) placeResult
        cases unifyResult : unify placeState inferredTarget.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at success
        | ok unifiedState =>
            simp only [unifyResult, bind, Except.bind, pure, Pure.pure,
              Except.pure] at success
            have unifyProgress := unify_inferenceProgress
              placeProperties.2.1.solved placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              placeProperties.2.1 placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            injection success with resultEq
            rw [← resultEq]
            refine ⟨allocationProperties.1.trans
                (placeProperties.1.trans
                  (unifyProgress.trans
                    (State.InferenceProgress.recordNode _ _
                      unifiedReady.solved))),
              State.InferenceReady.recordNode _ unifiedReady,
              Ty.variablesBelow_constructor _ _⟩
  case case15 =>
    intros context expression expected initial fuel id allocated allocationEq
      keyword sourceParameters returnAnnotation body expressionEq bodyInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases parameterResult : bindLambdaParameters context
        sourceParameters.elements 0 [] allocated with
    | error error =>
        simp [parameterResult, bind, Except.bind] at success
    | ok parameterTriple =>
        rcases parameterTriple with
          ⟨boundParameters, parameterTypes, parameterState⟩
        simp only [parameterResult, bind, Except.bind] at success
        have parameterProperties :=
          bindLambdaParameters_inferenceProperties allocatedReady
            parameterResult
        have parameterProgress :
            allocated.InferenceProgress parameterState :=
          parameterProperties.1
        have parameterReady : parameterState.InferenceReady :=
          parameterProperties.2.1
        let parameterType := Ty.productMany parameterTypes
        have parameterTypeBelow : parameterType.VariablesBelow
            parameterState.inference.next := by
          exact Ty.variablesBelow_productMany parameterProperties.2.2
        let expectedParts := expected.bind fun type =>
          functionParts? (parameterState.resolve type)
        have parameterTypeEq :
            Ty.productMany parameterTypes = parameterType := rfl
        rw [parameterTypeEq] at success
        have expectedPartsEq :
            (expected.bind fun type =>
              functionParts? (parameterState.resolve type)) =
              expectedParts := rfl
        rw [expectedPartsEq] at success
        have expectedPartsBelow {expectedParameter expectedResult : Ty}
            (partsEq : expectedParts =
              some (expectedParameter, expectedResult)) :
            expectedParameter.VariablesBelow parameterState.inference.next ∧
              expectedResult.VariablesBelow
                parameterState.inference.next := by
          unfold expectedParts at partsEq
          simp only [Option.bind_eq_some_iff] at partsEq
          obtain ⟨expectedType, expectedEq, typePartsEq⟩ := partsEq
          have expectedAtParameter : expectedType.VariablesBelow
              parameterState.inference.next :=
            (expectedBelow expectedType (by simp [expectedEq])).weaken
              (allocationProgress.trans parameterProgress).next_le
          have resolvedExpectedBelow :
              (parameterState.resolve expectedType).VariablesBelow
                parameterState.inference.next :=
            parameterReady.solved.variablesBelow_apply expectedAtParameter
          exact functionParts?_success_variablesBelow resolvedExpectedBelow
            typePartsEq
        have finishBody (fittedState : State)
            (fitProgress : parameterState.InferenceProgress fittedState)
            (fittedReady : fittedState.InferenceReady)
            (resultType : Ty) (resultState : State)
            (resultProgress : fittedState.InferenceProgress resultState)
            (resultReady : resultState.InferenceReady)
            (resultTypeBelow : resultType.VariablesBelow
              resultState.inference.next)
            (tailSuccess :
              (do
                let lambdaContext := { context with loopDepth := 0 }
                let bodyResult ← inferStatementsFuel fuel lambdaContext
                  body.value resultType resultState
                let next ← unify bodyResult.state bodyResult.type resultType
                let next := next.restoreLexicalScope allocated.lexicalScope
                recordExpressionWithExpected context expression id
                  (.function (next.resolve parameterType)
                    (next.resolve resultType))
                  (.lambda boundParameters (next.resolve resultType)
                    bodyResult.statements) [] expected next) = .ok result) :
            initial.InferenceProgress result.2 ∧
              result.2.InferenceReady ∧
              result.1.type.VariablesBelow result.2.inference.next := by
          let lambdaContext := { context with loopDepth := 0 }
          have lambdaValidated : ProgramSignatureFormationValidated
              lambdaContext.signatures := by
            simpa only [lambdaContext] using validated
          have lambdaCanonical : FunctionSchemesCanonical lambdaContext := by
            intro signature member
            exact canonical signature member
          cases bodyResult : inferStatementsFuel fuel lambdaContext body.value
              resultType resultState with
          | error error =>
              simp [lambdaContext, bodyResult, bind, Except.bind]
                at tailSuccess
          | ok inferredBody =>
              simp only [lambdaContext, bodyResult, bind, Except.bind]
                at tailSuccess
              have bodyProperties := bodyInduction resultType resultState
                resultReady lambdaValidated lambdaCanonical resultTypeBelow
                inferredBody bodyResult
              have resultAtBody : resultType.VariablesBelow
                  inferredBody.state.inference.next :=
                resultTypeBelow.weaken bodyProperties.1.next_le
              cases unifiedResult : unify inferredBody.state
                  inferredBody.type resultType with
              | error error =>
                  simp [unifiedResult, bind, Except.bind] at tailSuccess
              | ok unifiedState =>
                  simp only [unifiedResult, bind, Except.bind] at tailSuccess
                  have unifiedProgress := unify_inferenceProgress
                    bodyProperties.2.1.solved bodyProperties.2.2
                    resultAtBody unifiedResult
                  have unifiedReady := unify_preserves_inferenceReady
                    bodyProperties.2.1 bodyProperties.2.2 resultAtBody
                    unifiedResult
                  let restoredState := unifiedState.restoreLexicalScope
                    allocated.lexicalScope
                  have throughUnified :
                      allocated.InferenceProgress unifiedState :=
                    parameterProgress.trans
                      (fitProgress.trans
                        (resultProgress.trans
                          (bodyProperties.1.trans unifiedProgress)))
                  have restoredProperties :
                      allocated.InferenceProgress restoredState ∧
                        restoredState.InferenceReady := by
                    simpa only [restoredState] using
                      State.restoreLexicalScope_inferenceProperties
                        allocatedReady throughUnified
                  have restoreStep :
                      unifiedState.InferenceProgress restoredState := by
                    simpa only [restoredState] using
                      State.InferenceProgress.restoreLexicalScope unifiedState
                        allocated.lexicalScope unifiedReady.solved
                  have parameterToRestored :
                      parameterState.InferenceProgress restoredState :=
                    fitProgress.trans
                      (resultProgress.trans
                        (bodyProperties.1.trans
                          (unifiedProgress.trans restoreStep)))
                  have resultToRestored :
                      resultState.InferenceProgress restoredState :=
                    bodyProperties.1.trans
                      (unifiedProgress.trans restoreStep)
                  have resolvedParameterBelow :
                      (restoredState.resolve parameterType).VariablesBelow
                        restoredState.inference.next :=
                    parameterToRestored.resolve_variablesBelow
                      parameterTypeBelow
                  have resolvedResultBelow :
                      (restoredState.resolve resultType).VariablesBelow
                        restoredState.inference.next :=
                    resultToRestored.resolve_variablesBelow resultTypeBelow
                  have functionBelow :
                      (Ty.function (restoredState.resolve parameterType)
                        (restoredState.resolve resultType)).VariablesBelow
                          restoredState.inference.next :=
                    (Ty.variablesBelow_function_iff _ _ _).2
                      ⟨resolvedParameterBelow, resolvedResultBelow⟩
                  have prefixProgress :
                      initial.InferenceProgress restoredState :=
                    allocationProgress.trans restoredProperties.1
                  have expectedAtRestored : ∀ expectedType ∈ expected,
                      expectedType.VariablesBelow
                        restoredState.inference.next := by
                    intro expectedType member
                    exact (expectedBelow expectedType member).weaken
                      prefixProgress.next_le
                  have recordSuccess :
                      recordExpressionWithExpected context expression id
                        (.function (restoredState.resolve parameterType)
                          (restoredState.resolve resultType))
                        (.lambda boundParameters
                          (restoredState.resolve resultType)
                          inferredBody.statements)
                        [] expected restoredState = .ok result := by
                    simpa only [restoredState] using tailSuccess
                  have recordedProperties :=
                    recordExpressionWithExpected_inferenceProperties
                      restoredProperties.2 functionBelow expectedAtRestored
                      recordSuccess
                  exact ⟨prefixProgress.trans recordedProperties.1,
                    recordedProperties.2⟩
        cases partsEq : expectedParts with
        | none =>
            simp only [partsEq, bind, Except.bind, pure, Pure.pure,
              Except.pure] at success
            cases returnAnnotation with
            | some sourceType =>
                cases annotationResult : resolveSourceType context sourceType with
                | error error =>
                    simp [annotationResult, bind, Except.bind] at success
                | ok annotatedType =>
                    simp only [annotationResult, bind, Except.bind, pure,
                      Pure.pure, Except.pure, Prod.eta] at success
                    exact finishBody parameterState
                      (State.InferenceProgress.refl parameterReady.solved)
                      parameterReady annotatedType parameterState
                      (State.InferenceProgress.refl parameterReady.solved)
                      parameterReady
                      (resolveSourceType_success_variablesBelow
                        annotationResult _)
                      success
            | none =>
                simp only [partsEq, bind, Except.bind, pure, Pure.pure,
                  Except.pure, Prod.eta] at success
                have freshProgress :=
                  State.InferenceProgress.fresh parameterState
                    parameterReady.solved
                have freshReady := State.InferenceReady.fresh parameterReady
                have freshBelow :
                    parameterState.fresh.1.VariablesBelow
                      parameterState.fresh.2.inference.next := by
                  change Ty.VariablesBelow (parameterState.inference.next + 1)
                    (.variable ⟨parameterState.inference.next⟩)
                  exact (Ty.variablesBelow_variable_iff _ _).2
                    (Nat.lt_succ_self _)
                exact finishBody parameterState
                  (State.InferenceProgress.refl parameterReady.solved)
                  parameterReady parameterState.fresh.1
                  parameterState.fresh.2 freshProgress freshReady freshBelow
                  success
        | some parts =>
            rcases parts with ⟨expectedParameter, expectedResult⟩
            simp only [partsEq, bind, Except.bind] at success
            cases unifiedResult : unify parameterState parameterType
                expectedParameter with
            | error error =>
                simp [unifiedResult, bind, Except.bind] at success
            | ok fittedState =>
                simp only [unifiedResult, bind, Except.bind] at success
                have partsBelow := expectedPartsBelow partsEq
                have fitProgress := unify_inferenceProgress
                  parameterReady.solved parameterTypeBelow partsBelow.1
                  unifiedResult
                have fittedReady := unify_preserves_inferenceReady
                  parameterReady parameterTypeBelow partsBelow.1 unifiedResult
                cases returnAnnotation with
                | some sourceType =>
                    cases annotationResult : resolveSourceType context sourceType with
                    | error error =>
                        simp [annotationResult, bind, Except.bind] at success
                    | ok annotatedType =>
                        simp only [annotationResult, bind, Except.bind, pure,
                          Pure.pure, Except.pure, Prod.eta] at success
                        exact finishBody fittedState fitProgress fittedReady
                          annotatedType fittedState
                          (State.InferenceProgress.refl fittedReady.solved)
                          fittedReady
                          (resolveSourceType_success_variablesBelow
                            annotationResult _)
                          success
                | none =>
                    simp only [partsEq, bind, Except.bind, pure, Pure.pure,
                      Except.pure, Prod.eta] at success
                    exact finishBody fittedState fitProgress fittedReady
                      expectedResult fittedState
                      (State.InferenceProgress.refl fittedReady.solved)
                      fittedReady
                      (partsBelow.2.weaken fitProgress.next_le)
                      success
  -- Direct, indirect, builtin, and constructor application.
  case case16 =>
    intros context expression expected initial fuel id allocated allocationEq
      callee sourceArguments expressionEq constructorInduction
      argumentsInduction calleeInduction
    unfold InferExprFuelInferenceProperties
    intro ready validated canonical expectedBelow result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidatesResult :
        constructorCalleeCandidates context allocated callee with
    | error error =>
        simp [candidatesResult, bind, Except.bind] at success
    | ok candidates =>
        simp only [candidatesResult, bind, Except.bind] at success
        cases candidates with
        | cons candidate rest =>
            cases rest with
            | cons second tail =>
                simp at success
            | nil =>
                rcases candidate with ⟨dataType, constructor⟩
                let freshResult :=
                  freshDataConstructorInstantiation dataType constructor
                    allocated
                have candidateFacts :=
                  constructorCalleeCandidates_success_members candidatesResult
                    dataType constructor (by simp)
                have payloadTypesBelow :=
                  validated.data_constructor_payloadTypes_variablesBelow
                    candidateFacts.1 candidateFacts.2
                    allocated.inference.next
                have freshProperties :=
                  freshDataConstructorInstantiation_inferenceProperties
                    dataType constructor allocated allocationProperties.2
                    payloadTypesBelow
                have constructorProperties := constructorInduction
                  freshResult.1 freshResult.2 freshProperties.2.1 validated
                  canonical freshProperties.2.2.2.1 freshProperties.2.2.2.2
                  (by
                    intro expectedType member
                    exact (expectedAtAllocated expectedType member).weaken
                      freshProperties.1.next_le)
                  result
                  (by
                    simpa only [freshResult] using success)
                exact ⟨allocationProperties.1.trans
                    (freshProperties.1.trans constructorProperties.1),
                  constructorProperties.2⟩
        | nil =>
            simp only [bind, Except.bind] at success
            split at success
            · cases success
            · next _ missing _ =>
              cases missing with
              | some missing =>
                  rcases missing with ⟨qualifiers, name⟩
                  simp at success
              | none =>
                cases argumentsResult : inferExprsFuel fuel context
                    sourceArguments.elements allocated with
                | error error =>
                    simp [argumentsResult, bind, Except.bind] at success
                | ok argumentsPair =>
                    rcases argumentsPair with ⟨arguments, argumentState⟩
                    simp only [argumentsResult, bind, Except.bind,
                      Prod.eta] at success
                    have argumentsProperties := argumentsInduction
                      allocationProperties.2 validated canonical
                      (arguments, argumentState) argumentsResult
                    have prefixProgress := allocationProperties.1.trans
                      argumentsProperties.1
                    have expectedAtArguments : ∀ expectedType ∈ expected,
                        expectedType.VariablesBelow
                          argumentState.inference.next := by
                      intro expectedType member
                      exact (expectedBelow expectedType member).weaken
                        prefixProgress.next_le
                    have finishSelected
                        (name : String)
                        (candidates : List ProgramFunctionSignature)
                        (subset : candidates ⊆ context.signatures.functions)
                        (attempt : CandidateAttemptResult)
                        (selectionSuccess :
                          selectFunctionCandidateFrom context name candidates
                            arguments
                            (relevantIntegerLiterals argumentState
                              allocated.integerLiterals.length arguments)
                            id expected argumentState = .ok attempt)
                        (resultEq :
                          recordSelectedCall expression callee name arguments
                            attempt = result) :
                        initial.InferenceProgress result.2 ∧
                          result.2.InferenceReady ∧
                          result.1.type.VariablesBelow
                            result.2.inference.next := by
                      have selectedProperties :=
                        selectFunctionCandidateFrom_inferenceProperties
                          argumentsProperties.2.1
                          argumentsProperties.2.2
                          (functionCandidates_scheme_body_variablesBelow
                            validated canonical subset _)
                          expectedAtArguments selectionSuccess
                      have recordedProperties :=
                        recordSelectedCall_inferenceProperties expression
                          callee name arguments attempt
                          selectedProperties.2.1 selectedProperties.2.2
                      rw [← resultEq]
                      exact ⟨prefixProgress.trans
                          (selectedProperties.1.trans recordedProperties.1),
                        recordedProperties.2⟩
                    have finishIndirect
                        (calleeResult : InferredExpression)
                        (calleeState : State)
                        (calleeSuccess :
                          inferExprFuel fuel context callee none argumentState =
                            .ok (calleeResult, calleeState))
                        (application : IndirectApplicationResult)
                        (applicationSuccess :
                          applyFunctionType context id calleeResult.type
                            arguments expected calleeState = .ok application)
                        (resultEq :
                          recordIndirectCall expression calleeResult arguments
                            application = result) :
                        initial.InferenceProgress result.2 ∧
                          result.2.InferenceReady ∧
                          result.1.type.VariablesBelow
                            result.2.inference.next := by
                      have calleeProperties := calleeInduction argumentState
                        argumentsProperties.2.1 validated canonical (by simp)
                        (calleeResult, calleeState) calleeSuccess
                      have applicationProperties :=
                        applyFunctionType_inferenceProperties
                          calleeProperties.2.1 calleeProperties.2.2
                          (by
                            intro argument member
                            exact (argumentsProperties.2.2 argument member).weaken
                              calleeProperties.1.next_le)
                          (by
                            intro expectedType member
                            exact (expectedAtArguments expectedType member).weaken
                              calleeProperties.1.next_le)
                          applicationSuccess
                      have recordedProperties :=
                        recordIndirectCall_inferenceProperties expression
                          calleeResult arguments application
                          applicationProperties.2.1 applicationProperties.2.2
                      rw [← resultEq]
                      exact ⟨prefixProgress.trans
                          (calleeProperties.1.trans
                            (applicationProperties.1.trans
                              recordedProperties.1)),
                        recordedProperties.2⟩
                    cases qualifiedEq : calleeQualifiedIdentifier? callee with
                    | some qualified =>
                        rcases qualified with ⟨namespacePath, name⟩
                        simp only [qualifiedEq] at success
                        cases binderEq :
                            argumentState.lookupBinder? namespacePath.head! with
                        | some binder =>
                            simp only [binderEq] at success
                            cases calleeResult : inferExprFuel fuel context callee
                                none argumentState with
                            | error error =>
                                simp [calleeResult, bind, Except.bind] at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult, bind, Except.bind,
                                  Prod.eta] at success
                                cases applicationResult : applyFunctionType
                                    context id inferredCallee.type arguments
                                    expected calleeState with
                                | error error =>
                                    simp [applicationResult, bind, Except.bind]
                                      at success
                                | ok application =>
                                    simp only [applicationResult, bind,
                                      Except.bind, pure, Pure.pure, Except.pure]
                                      at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult application
                                      applicationResult resultEq
                        | none =>
                            simp only [binderEq] at success
                            cases functionsResult : qualifiedFunctionsNamed
                                context namespacePath name with
                            | error error =>
                                simp [functionsResult, bind, Except.bind]
                                  at success
                            | ok candidatesOption =>
                                simp only [functionsResult, bind, Except.bind]
                                  at success
                                cases candidatesOption with
                                | some candidates =>
                                    cases selectionResult :
                                        selectFunctionCandidateFrom context
                                          (String.intercalate "."
                                            (namespacePath ++ [name]))
                                          candidates arguments
                                          (relevantIntegerLiterals
                                            argumentState
                                            allocated.integerLiterals.length
                                            arguments)
                                          id expected argumentState with
                                    | error error =>
                                        simp [selectionResult, bind,
                                          Except.bind] at success
                                    | ok attempt =>
                                        simp only [selectionResult, bind,
                                          Except.bind, pure, Pure.pure,
                                          Except.pure] at success
                                        injection success with resultEq
                                        exact finishSelected
                                          (String.intercalate "."
                                            (namespacePath ++ [name]))
                                          candidates
                                          (qualifiedFunctionsNamed_success_subset_catalog
                                            functionsResult)
                                          attempt selectionResult resultEq
                                | none =>
                                    cases calleeResult : inferExprFuel fuel
                                        context callee none argumentState with
                                    | error error =>
                                        simp [calleeResult, bind, Except.bind]
                                          at success
                                    | ok calleePair =>
                                        rcases calleePair with
                                          ⟨inferredCallee, calleeState⟩
                                        simp only [calleeResult, bind,
                                          Except.bind, Prod.eta] at success
                                        cases applicationResult :
                                            applyFunctionType context id
                                              inferredCallee.type arguments
                                              expected calleeState with
                                        | error error =>
                                            simp [applicationResult, bind,
                                              Except.bind] at success
                                        | ok application =>
                                            simp only [applicationResult, bind,
                                              Except.bind, pure, Pure.pure,
                                              Except.pure] at success
                                            injection success with resultEq
                                            exact finishIndirect inferredCallee
                                              calleeState calleeResult
                                              application applicationResult
                                              resultEq
                    | none =>
                        simp only [qualifiedEq] at success
                        cases identifierEq : calleeIdentifier? callee with
                        | none =>
                            simp only [identifierEq] at success
                            cases calleeResult : inferExprFuel fuel context callee
                                none argumentState with
                            | error error =>
                                simp [calleeResult, bind, Except.bind] at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult, bind, Except.bind,
                                  Prod.eta] at success
                                cases applicationResult : applyFunctionType
                                    context id inferredCallee.type arguments
                                    expected calleeState with
                                | error error =>
                                    simp [applicationResult, bind, Except.bind]
                                      at success
                                | ok application =>
                                    simp only [applicationResult, bind,
                                      Except.bind, pure, Pure.pure, Except.pure]
                                      at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult application
                                      applicationResult resultEq
                        | some name =>
                            simp only [identifierEq] at success
                            cases binderEq : argumentState.lookupBinder? name with
                            | some binder =>
                                simp only [binderEq] at success
                                cases calleeResult : inferExprFuel fuel context
                                    callee none argumentState with
                                | error error =>
                                    simp [calleeResult, bind, Except.bind]
                                      at success
                                | ok calleePair =>
                                    rcases calleePair with
                                      ⟨inferredCallee, calleeState⟩
                                    simp only [calleeResult, bind, Except.bind,
                                      Prod.eta] at success
                                    cases applicationResult : applyFunctionType
                                        context id inferredCallee.type arguments
                                        expected calleeState with
                                    | error error =>
                                        simp [applicationResult, bind,
                                          Except.bind] at success
                                    | ok application =>
                                        simp only [applicationResult, bind,
                                          Except.bind, pure, Pure.pure,
                                          Except.pure] at success
                                        injection success with resultEq
                                        exact finishIndirect inferredCallee
                                          calleeState calleeResult application
                                          applicationResult resultEq
                            | none =>
                                simp only [binderEq] at success
                                cases functionsResult : functionsNamed context
                                    name with
                                | error error =>
                                    simp [functionsResult, bind, Except.bind]
                                      at success
                                | ok candidates =>
                                    simp only [functionsResult, bind,
                                      Except.bind] at success
                                    cases candidates with
                                    | nil =>
                                        cases builtinEq :
                                            builtinFunctionNamed? name with
                                        | none =>
                                            simp [builtinEq] at success
                                        | some function =>
                                            simp only [builtinEq] at success
                                            have builtinProperties :=
                                              recordBuiltinFunctionCall_inferenceProperties
                                                argumentsProperties.2.1
                                                argumentsProperties.2.2
                                                expectedAtArguments success
                                            exact ⟨prefixProgress.trans
                                                builtinProperties.1,
                                              builtinProperties.2⟩
                                    | cons candidate rest =>
                                        cases selectionResult :
                                            selectFunctionCandidateFrom context
                                              name (candidate :: rest) arguments
                                              (relevantIntegerLiterals
                                                argumentState
                                                allocated.integerLiterals.length
                                                arguments)
                                              id expected argumentState with
                                        | error error =>
                                            simp [selectionResult, bind,
                                              Except.bind] at success
                                        | ok attempt =>
                                            simp only [selectionResult, bind,
                                              Except.bind, pure, Pure.pure,
                                              Except.pure] at success
                                            injection success with resultEq
                                            exact finishSelected name
                                              (candidate :: rest)
                                              (functionsNamed_success_subset_catalog
                                                functionsResult)
                                              attempt selectionResult resultEq
  case case43 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq scrutinees arms statementEq sources source sourcesEq
      casesInduction bodyInduction scrutineeInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateStatementId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateStatementId ready
      rw [allocationEq] at nextReady
      exact nextReady
    unfold inferStatementFuel at success
    have rawSourcesEq : scrutinees.elements.toList = [source] := by
      simpa only [sources] using sourcesEq
    simp only [allocationEq, statementEq, rawSourcesEq, bind, Except.bind]
      at success
    cases scrutineeResult :
        inferExprFuel fuel context source none allocated with
    | error error =>
        simp [scrutineeResult, bind, Except.bind] at success
    | ok scrutineePair =>
        rcases scrutineePair with ⟨scrutinee, scrutineeState⟩
        try simp only [scrutineeResult, bind, Except.bind, Prod.eta] at success
        have scrutineeProperties := scrutineeInduction allocatedReady
          validated canonical (by simp) (scrutinee, scrutineeState)
          scrutineeResult
        let hiddenState := scrutineeState.allocateHiddenLocal.2
        have hiddenProgress :
            scrutineeState.InferenceProgress hiddenState := by
          simpa only [hiddenState] using
            State.InferenceProgress.allocateHiddenLocal scrutineeState
              scrutineeProperties.2.1.solved
        have hiddenReady : hiddenState.InferenceReady := by
          simpa only [hiddenState] using
            State.InferenceReady.allocateHiddenLocal scrutineeProperties.2.1
        have throughHidden := allocationProgress.trans
          (scrutineeProperties.1.trans hiddenProgress)
        cases checkedResult : inferMatchCasesFuel fuel context scrutinee.type
            expectedReturn hiddenState.lexicalScope arms.value.cases
            hiddenState with
        | error error =>
            simp [hiddenState, checkedResult, bind, Except.bind] at success
        | ok checked =>
            simp only [hiddenState, checkedResult, bind, Except.bind]
              at success
            have casesProperties := casesInduction scrutinee hiddenState
              hiddenReady validated canonical
              (scrutineeProperties.2.2.weaken hiddenProgress.next_le)
              (returnBelow.weaken throughHidden.next_le) rfl checked
              checkedResult
            have throughChecked := throughHidden.trans casesProperties.1
            cases defaultEq : arms.value.defaultBody with
            | none =>
                simp only [defaultEq, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
                split at success
                · cases success
                · injection success with resultEq
                  rw [← resultEq]
                  refine ⟨throughChecked.trans
                      (State.InferenceProgress.recordNode _ _
                        casesProperties.2.1.solved),
                    State.InferenceReady.recordNode _ casesProperties.2.1,
                    ?_⟩
                  split
                  · exact throughChecked.resolve_variablesBelow returnBelow
                  · exact Ty.variablesBelow_constructor _ _
            | some body =>
                cases bodyResult : inferStatementsFuel fuel context body.value
                    expectedReturn checked.state with
                | error error =>
                    simp [defaultEq, bodyResult, bind, Except.bind] at success
                | ok inferred =>
                    simp only [defaultEq, bodyResult, bind, Except.bind,
                      Prod.eta, pure, Pure.pure, Except.pure] at success
                    have bodyProperties := bodyInduction checked body
                      casesProperties.2.1 validated canonical
                      (returnBelow.weaken throughChecked.next_le) inferred
                      bodyResult
                    have restoredProperties :=
                      State.restoreLexicalScope_inferenceProperties
                        casesProperties.2.1 bodyProperties.1
                    rw [casesProperties.2.2] at restoredProperties
                    have throughDefault :=
                      throughChecked.trans restoredProperties.1
                    split at success
                    · cases success
                    · injection success with resultEq
                      rw [← resultEq]
                      refine ⟨throughDefault.trans
                          (State.InferenceProgress.recordNode _ _
                            restoredProperties.2.solved),
                        State.InferenceReady.recordNode _
                          restoredProperties.2, ?_⟩
                      split
                      · exact throughDefault.resolve_variablesBelow returnBelow
                      · exact Ty.variablesBelow_constructor _ _
  case case44 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateStatementId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateStatementId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have sourceDispatch :
        (match sources with
        | [source] => inferExprFuel fuel context source none allocated
        | sources => do
            let (elements, state) ←
              inferExprsFuel fuel context sources allocated
            let (tupleId, state) := state.allocateExpressionId
            let type := Ty.productMany
              (elements.map (fun element : InferredExpression => element.type))
            let state := state.recordNode (.expression {
              id := tupleId
              span := statement.span
              type
              form := .tuple
                (elements.map (fun element : InferredExpression => element.id))
            })
            pure ({ id := tupleId, type }, state)) =
          (do
            let (elements, state) ←
              inferExprsFuel fuel context sources allocated
            let (tupleId, state) := state.allocateExpressionId
            let type := Ty.productMany
              (elements.map (fun element : InferredExpression => element.type))
            let state := state.recordNode (.expression {
              id := tupleId
              span := statement.span
              type
              form := .tuple
                (elements.map (fun element : InferredExpression => element.id))
            })
            pure ({ id := tupleId, type }, state)) := by
      cases sourcesEq : sources with
      | nil => simp only [sourcesEq]
      | cons first rest =>
          cases rest with
          | nil =>
              exact (notSingleton first (by simpa using sourcesEq)).elim
          | cons second tail => simp only [sourcesEq]
    unfold inferStatementFuel at success
    have rawSourcesEq : scrutinees.elements.toList = sources := by
      rfl
    simp only [allocationEq, statementEq, rawSourcesEq, sourceDispatch, bind,
      Except.bind] at success
    cases expressionsResult : inferExprsFuel fuel context sources allocated with
    | error error =>
        simp [expressionsResult, bind, Except.bind] at success
    | ok expressionsPair =>
        rcases expressionsPair with ⟨elements, elementState⟩
        simp only [expressionsResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        have expressionsProperties := expressionsInduction allocatedReady
          validated canonical (elements, elementState) expressionsResult
        let tupleResult : InferredExpression × State := ({
            id := elementState.allocateExpressionId.fst
            type := Ty.productMany (elements.map (·.type))
          }, elementState.allocateExpressionId.snd.recordNode (.expression {
            id := elementState.allocateExpressionId.fst
            span := statement.span
            type := Ty.productMany (elements.map (·.type))
            form := .tuple (elements.map (·.id))
          }))
        have tupleProperties := syntheticTuple_result_inferenceProperties
          (elements := elements) (span := statement.span)
          (state := elementState) expressionsProperties.2.1
          expressionsProperties.2.2
          (result := tupleResult)
          (by simp only [tupleResult, except_pure_eq_ok])
        let hiddenState := tupleResult.2.allocateHiddenLocal.2
        have hiddenProgress : tupleResult.2.InferenceProgress hiddenState := by
          simpa only [hiddenState] using
            State.InferenceProgress.allocateHiddenLocal tupleResult.2
              tupleProperties.2.1.solved
        have hiddenReady : hiddenState.InferenceReady := by
          simpa only [hiddenState] using
            State.InferenceReady.allocateHiddenLocal tupleProperties.2.1
        have throughHidden := allocationProgress.trans
          (expressionsProperties.1.trans
            (tupleProperties.1.trans hiddenProgress))
        cases checkedResult : inferMatchCasesFuel fuel context
            tupleResult.1.type expectedReturn hiddenState.lexicalScope
            arms.value.cases hiddenState with
        | error error =>
            rw [checkedResult] at success
            simp at success
        | ok checked =>
            rw [checkedResult] at success
            simp only [bind, Except.bind] at success
            have casesProperties := casesInduction tupleResult.1 hiddenState
              hiddenReady validated canonical
              (tupleProperties.2.2.weaken hiddenProgress.next_le)
              (returnBelow.weaken throughHidden.next_le) rfl checked
              checkedResult
            have throughChecked := throughHidden.trans casesProperties.1
            cases defaultEq : arms.value.defaultBody with
            | none =>
                simp only [defaultEq, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
                split at success
                · cases success
                · injection success with resultEq
                  rw [← resultEq]
                  refine ⟨throughChecked.trans
                      (State.InferenceProgress.recordNode _ _
                        casesProperties.2.1.solved),
                    State.InferenceReady.recordNode _ casesProperties.2.1,
                    ?_⟩
                  split
                  · exact throughChecked.resolve_variablesBelow returnBelow
                  · exact Ty.variablesBelow_constructor _ _
            | some body =>
                cases bodyResult : inferStatementsFuel fuel context body.value
                    expectedReturn checked.state with
                | error error =>
                    simp [defaultEq, bodyResult, bind, Except.bind] at success
                | ok inferred =>
                    simp only [defaultEq, bodyResult, bind, Except.bind,
                      Prod.eta, pure, Pure.pure, Except.pure] at success
                    have bodyProperties := bodyInduction checked body
                      casesProperties.2.1 validated canonical
                      (returnBelow.weaken throughChecked.next_le) inferred
                      bodyResult
                    have restoredProperties :=
                      State.restoreLexicalScope_inferenceProperties
                        casesProperties.2.1 bodyProperties.1
                    rw [casesProperties.2.2] at restoredProperties
                    have throughDefault :=
                      throughChecked.trans restoredProperties.1
                    split at success
                    · cases success
                    · injection success with resultEq
                      rw [← resultEq]
                      refine ⟨throughDefault.trans
                          (State.InferenceProgress.recordNode _ _
                            restoredProperties.2.solved),
                        State.InferenceReady.recordNode _
                          restoredProperties.2, ?_⟩
                      split
                      · exact throughDefault.resolve_variablesBelow returnBelow
                      · exact Ty.variablesBelow_constructor _ _
  case case45 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq headerSpan initializer condition post body statementEq
      initializerInduction conditionInduction bodyInduction postInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let loopContext := { context with loopDepth := context.loopDepth + 1 }
    have loopValidated :
        ProgramSignatureFormationValidated loopContext.signatures := by
      simpa only [loopContext] using validated
    have loopCanonical : FunctionSchemesCanonical loopContext := by
      intro signature member
      exact canonical signature member
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases initializerResult : inferForItemsFuel fuel context initializer allocated with
    | error error =>
        simp [initializerResult, bind, Except.bind] at success
    | ok initialized =>
      simp only [initializerResult, bind, Except.bind] at success
      have initializerProperties := initializerInduction allocationProperties.2
        validated canonical initialized initializerResult
      cases conditionResult : inferExprFuel fuel context condition (some .bool)
          initialized.state with
      | error error =>
          simp [conditionResult, bind, Except.bind] at success
      | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult, bind, Except.bind, Prod.eta] at success
        have conditionProperties := conditionInduction initialized
          initializerProperties.2 validated canonical
          (by
            intro expectedType member
            simp at member
            subst expectedType
            exact Ty.variablesBelow_constructor _ _)
          (inferredCondition, conditionState) conditionResult
        have throughCondition := allocationProperties.1.trans
          (initializerProperties.1.trans conditionProperties.1)
        cases bodyResult : inferStatementsFuel fuel loopContext body.value
            expectedReturn conditionState with
        | error error =>
            simp [loopContext, bodyResult, bind, Except.bind] at success
        | ok inferredBody =>
          simp only [loopContext, bodyResult, bind, Except.bind] at success
          have bodyProperties := bodyInduction conditionState
            conditionProperties.2.1 loopValidated loopCanonical
            (returnBelow.weaken throughCondition.next_le) inferredBody bodyResult
          let afterBody := inferredBody.state.restoreLexicalScope
            initialized.state.lexicalScope
          have restoredBody : initialized.state.InferenceProgress afterBody ∧
              afterBody.InferenceReady := by
            simpa only [afterBody] using
              State.restoreLexicalScope_inferenceProperties
                initializerProperties.2
                (conditionProperties.1.trans bodyProperties.1)
          cases postResult : inferForItemsFuel fuel loopContext post afterBody with
          | error error =>
              simp [loopContext, afterBody, postResult, bind, Except.bind]
                at success
          | ok inferredPost =>
            simp only [loopContext, afterBody, postResult, bind, Except.bind]
              at success
            have postProperties := postInduction initialized inferredBody
              restoredBody.2 loopValidated loopCanonical inferredPost postResult
            have throughPost : allocated.InferenceProgress inferredPost.state :=
              initializerProperties.1.trans
                (restoredBody.1.trans postProperties.1)
            let preRecordState := inferredPost.state.restoreLexicalScope
              allocated.lexicalScope
            have restoredOuter : allocated.InferenceProgress preRecordState ∧
                preRecordState.InferenceReady := by
              simpa only [preRecordState] using
                State.restoreLexicalScope_inferenceProperties
                  allocationProperties.2 throughPost
            injection success with resultEq
            rw [← resultEq]
            refine ⟨allocationProperties.1.trans
                (restoredOuter.1.trans
                  (State.InferenceProgress.recordNode _ _
                    restoredOuter.2.solved)),
              State.InferenceReady.recordNode _ restoredOuter.2,
              Ty.variablesBelow_constructor _ _⟩
  case case46 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition body statementEq conditionInduction bodyInduction
    unfold InferStatementFuelInferenceProperties
    intro ready validated canonical returnBelow result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let loopContext := { context with loopDepth := context.loopDepth + 1 }
    have loopValidated :
        ProgramSignatureFormationValidated loopContext.signatures := by
      simpa only [loopContext] using validated
    have loopCanonical : FunctionSchemesCanonical loopContext := by
      intro signature member
      exact canonical signature member
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition (some .bool)
        allocated with
    | error error =>
        simp [conditionResult, bind, Except.bind] at success
    | ok conditionPair =>
      rcases conditionPair with ⟨inferredCondition, conditionState⟩
      simp only [conditionResult, bind, Except.bind, Prod.eta] at success
      have conditionProperties := conditionInduction allocationProperties.2
        validated canonical
        (by
          intro expectedType member
          simp at member
          subst expectedType
          exact Ty.variablesBelow_constructor _ _)
        (inferredCondition, conditionState) conditionResult
      have throughCondition :=
        allocationProperties.1.trans conditionProperties.1
      cases bodyResult : inferStatementsFuel fuel loopContext body.value
          expectedReturn conditionState with
      | error error =>
          simp [loopContext, bodyResult, bind, Except.bind] at success
      | ok inferredBody =>
        simp only [loopContext, bodyResult, bind, Except.bind] at success
        have bodyProperties := bodyInduction conditionState
          conditionProperties.2.1 loopValidated loopCanonical
          (returnBelow.weaken throughCondition.next_le) inferredBody bodyResult
        let preRecordState := inferredBody.state.restoreLexicalScope
          conditionState.lexicalScope
        have restoredBody : conditionState.InferenceProgress preRecordState ∧
            preRecordState.InferenceReady := by
          simpa only [preRecordState] using
            State.restoreLexicalScope_inferenceProperties
              conditionProperties.2.1 bodyProperties.1
        injection success with resultEq
        rw [← resultEq]
        refine ⟨throughCondition.trans
            (restoredBody.1.trans
              (State.InferenceProgress.recordNode _ _
                restoredBody.2.solved)),
          State.InferenceReady.recordNode _ restoredBody.2,
          Ty.variablesBelow_constructor _ _⟩
  case case47 =>
    simp_all [InferStatementFuelInferenceProperties, inferStatementFuel]
  case case48 =>
    simp_all [InferStatementFuelInferenceProperties, inferStatementFuel,
      bind, Except.bind]
  case case49 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelInferenceProperties
    intro ready _ _ _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let finalState := allocated.recordNode (.statement {
      id
      span := statement.span
      type := .unit
      form := .breakStmt
    })
    have recordProgress : allocated.InferenceProgress finalState := by
      simpa only [finalState] using State.InferenceProgress.recordNode
        allocated (.statement {
          id
          span := statement.span
          type := .unit
          form := .breakStmt
        }) allocationProperties.2.solved
    have finalReady : finalState.InferenceReady := by
      simpa only [finalState] using State.InferenceReady.recordNode
        (.statement {
          id
          span := statement.span
          type := .unit
          form := .breakStmt
        }) allocationProperties.2
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, Bool.false_eq_true,
      if_false, finalState] at success
    injection success with resultEq
    subst result
    exact ⟨allocationProperties.1.trans recordProgress, finalReady,
      Ty.variablesBelow_constructor _ _⟩
  case case50 =>
    simp_all [InferStatementFuelInferenceProperties, inferStatementFuel,
      bind, Except.bind]
  case case51 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelInferenceProperties
    intro ready _ _ _ result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let finalState := allocated.recordNode (.statement {
      id
      span := statement.span
      type := .unit
      form := .continueStmt
    })
    have recordProgress : allocated.InferenceProgress finalState := by
      simpa only [finalState] using State.InferenceProgress.recordNode
        allocated (.statement {
          id
          span := statement.span
          type := .unit
          form := .continueStmt
        }) allocationProperties.2.solved
    have finalReady : finalState.InferenceReady := by
      simpa only [finalState] using State.InferenceReady.recordNode
        (.statement {
          id
          span := statement.span
          type := .unit
          form := .continueStmt
        }) allocationProperties.2
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, Bool.false_eq_true,
      if_false, finalState] at success
    injection success with resultEq
    subst result
    exact ⟨allocationProperties.1.trans recordProgress, finalReady,
      Ty.variablesBelow_constructor _ _⟩
  case case52 =>
    simp_all [InferStatementFuelInferenceProperties, inferStatementFuel]
  case case53 =>
    intros fuel context initial
    unfold InferForItemsFuelInferenceProperties
    intro ready _ _ result success
    unfold inferForItemsFuel at success
    injection success with resultEq
    subst result
    exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
  case case54 =>
    intros fuel context item items initial itemInduction tailInduction
    unfold InferForItemsFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemsFuel at success
    cases itemResult : inferForItemFuel fuel context item initial with
    | error error =>
        simp [itemResult, bind, Except.bind] at success
    | ok itemPair =>
        rcases itemPair with ⟨inferredItem, itemState⟩
        simp only [itemResult, bind, Except.bind] at success
        cases tailResult : inferForItemsFuel fuel context items itemState with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok tail =>
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            have itemProperties := itemInduction ready validated canonical
              (inferredItem, itemState) itemResult
            have tailProperties := tailInduction itemState
              itemProperties.2 validated canonical tail tailResult
            exact ⟨itemProperties.1.trans tailProperties.1,
              tailProperties.2⟩
  case case55 =>
    simp [InferForItemFuelInferenceProperties, inferForItemFuel]
  case case56 =>
    simp_all [InferForItemFuelInferenceProperties, inferForItemFuel, bind,
      Except.bind]
  case case57 =>
    intros context item initial fuel name sourceType itemEq
    unfold InferForItemFuelInferenceProperties
    intro ready _ _ result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult, bind, Except.bind] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, bind, Except.bind, pure, Pure.pure,
          Except.pure] at success
        let binding :=
          let locals := initial.binderEnvironment.apply
            initial.inference.substitution
          let valueType := initial.resolve resolvedType
          let generalized := generalizeValue initial locals
            initial.nextRequirement valueType
          (initial.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingProperties : initial.InferenceProgress binding.2 ∧
            binding.2.InferenceReady := by
          simpa only [binding] using
            generalizeValue_allocateBinder_inferenceProperties
              (state := initial) (requirementStart := initial.nextRequirement)
              (valueType := resolvedType) (name := name.value)
              (span := some name.span) ready
              (resolveSourceType_success_variablesBelow sourceTypeResult _)
        injection success with resultEq
        rw [← resultEq]
        exact bindingProperties
  case case58 =>
    intros context item initial fuel name initializer itemEq
      initializerInduction
    unfold InferForItemFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none
        initial with
    | error error =>
        simp [initializerResult, bind, Except.bind] at success
    | ok initializerPair =>
        rcases initializerPair with ⟨inferred, initializerState⟩
        simp only [initializerResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        have initializerProperties := initializerInduction ready validated
          canonical (by simp) (inferred, initializerState) initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            initial.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingProperties :
            initializerState.InferenceProgress binding.2 ∧
              binding.2.InferenceReady := by
          simpa only [binding] using
            generalizeValue_allocateBinder_inferenceProperties
              (state := initializerState)
              (requirementStart := initial.nextRequirement)
              (valueType := inferred.type) (name := name.value)
              (span := some name.span) initializerProperties.2.1
              initializerProperties.2.2
        injection success with resultEq
        rw [← resultEq]
        exact ⟨initializerProperties.1.trans bindingProperties.1,
          bindingProperties.2⟩
  case case59 =>
    intros context item initial fuel name sourceType initializer itemEq
      initializerInduction
    unfold InferForItemFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult, bind, Except.bind] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, bind, Except.bind] at success
        have resolvedTypeBelow :
            resolvedType.VariablesBelow initial.inference.next :=
          resolveSourceType_success_variablesBelow sourceTypeResult _
        cases initializerResult : inferExprFuel fuel context initializer
            (some resolvedType) initial with
        | error error =>
            simp [initializerResult, bind, Except.bind] at success
        | ok initializerPair =>
            rcases initializerPair with ⟨inferred, initializerState⟩
            simp only [initializerResult, bind, Except.bind, Prod.eta, pure,
              Pure.pure, Except.pure] at success
            have initializerProperties := initializerInduction resolvedType
              ready validated canonical
              (by
                intro expectedType member
                simp only [Option.mem_def] at member
                injection member with typeEq
                subst expectedType
                exact resolvedTypeBelow)
              (inferred, initializerState) initializerResult
            let binding :=
              let locals := initializerState.binderEnvironment.apply
                initializerState.inference.substitution
              let valueType := initializerState.resolve inferred.type
              let generalized := generalizeValue initializerState locals
                initial.nextRequirement valueType
              (initializerState.withLocals locals).allocateBinder name.value
                generalized.scheme (some name.span) false
                generalized.requirements
            have bindingProperties :
                initializerState.InferenceProgress binding.2 ∧
                  binding.2.InferenceReady := by
              simpa only [binding] using
                generalizeValue_allocateBinder_inferenceProperties
                  (state := initializerState)
                  (requirementStart := initial.nextRequirement)
                  (valueType := inferred.type) (name := name.value)
                  (span := some name.span) initializerProperties.2.1
                  initializerProperties.2.2
            injection success with resultEq
            rw [← resultEq]
            exact ⟨initializerProperties.1.trans bindingProperties.1,
              bindingProperties.2⟩
  case case60 =>
    intros context item initial fuel expression itemEq expressionInduction
    unfold InferForItemFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases expressionResult : inferExprFuel fuel context expression none initial with
    | error error =>
        simp [expressionResult, bind, Except.bind] at success
    | ok expressionPair =>
        rcases expressionPair with ⟨inferred, expressionState⟩
        simp only [expressionResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        injection success with resultEq
        rw [← resultEq]
        have expressionProperties := expressionInduction ready validated
          canonical (by simp) (inferred, expressionState) expressionResult
        exact ⟨expressionProperties.1, expressionProperties.2.1⟩
  case case61 =>
    intros context item initial fuel target operator value itemEq
      assignmentInduction
    unfold InferForItemFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases assignmentResult : inferAssignedValueFuel fuel context target
        operator.value value initial with
    | error error =>
        simp [assignmentResult, bind, Except.bind] at success
    | ok assignmentTriple =>
        rcases assignmentTriple with
          ⟨assignment, inferredValue, assignmentState⟩
        simp only [assignmentResult, bind, Except.bind, Prod.eta, pure,
          Pure.pure, Except.pure] at success
        injection success with resultEq
        rw [← resultEq]
        have assignmentProperties := assignmentInduction ready validated
          canonical (assignment, inferredValue, assignmentState)
          assignmentResult
        exact ⟨assignmentProperties.1, assignmentProperties.2.1⟩
  case case62 =>
    intros context item initial fuel target operator itemEq placeInduction
    unfold InferForItemFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases placeResult : inferPlaceFuel fuel context target initial with
    | error error =>
        simp [placeResult, bind, Except.bind] at success
    | ok placePair =>
        rcases placePair with ⟨place, placeState⟩
        simp only [placeResult, bind, Except.bind, Prod.eta] at success
        have placeProperties := placeInduction ready validated canonical
          (place, placeState) placeResult
        cases unifyResult : unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at success
        | ok unifiedState =>
            simp only [unifyResult, bind, Except.bind, pure, Pure.pure,
              Except.pure] at success
            injection success with resultEq
            rw [← resultEq]
            have unifyProgress := unify_inferenceProgress
              placeProperties.2.1.solved placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              placeProperties.2.1 placeProperties.2.2
              (Ty.variablesBelow_constructor _ _) unifyResult
            exact ⟨placeProperties.1.trans unifyProgress, unifiedReady⟩
  case case63 =>
    simp [InferPlaceFuelInferenceProperties, inferPlaceFuel]
  case case64 =>
    intros context target initial fuel name targetEq binder lookupEq
      monomorphic
    unfold InferPlaceFuelInferenceProperties
    intro ready _ _ result success
    unfold inferPlaceFuel at success
    simp only [targetEq, lookupEq, monomorphic, if_true] at success
    injection success with resultEq
    subst result
    have bodyBelow :=
      State.InferenceReady.lookupBinder?_body_variablesBelow ready lookupEq
    exact ⟨State.InferenceProgress.refl ready.solved, ready,
      ready.solved.variablesBelow_apply bodyBelow⟩
  case case65 =>
    simp_all [InferPlaceFuelInferenceProperties, inferPlaceFuel, bind,
      Except.bind]
  case case66 =>
    simp_all [InferPlaceFuelInferenceProperties, inferPlaceFuel, bind,
      Except.bind]
  case case67 =>
    intros fuel context target initial inner targetEq induction
    unfold InferPlaceFuelInferenceProperties at *
    intro ready validated canonical result success
    apply induction ready validated canonical result
    simpa only [inferPlaceFuel, targetEq] using success
  case case68 =>
    intros context target initial fuel base brackets key targetEq
      baseInduction keyInduction
    unfold InferPlaceFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferPlaceFuel at success
    simp only [targetEq, bind, Except.bind] at success
    cases baseResult : inferPlaceFuel fuel context base initial with
    | error error =>
        simp [baseResult, bind, Except.bind] at success
    | ok basePair =>
        rcases basePair with ⟨basePlace, baseState⟩
        simp only [baseResult, bind, Except.bind, Prod.eta] at success
        have baseProperties := baseInduction ready validated canonical
          (basePlace, baseState) baseResult
        let keyAllocation := baseState.fresh
        have keyProperties := fresh_eq_inferenceProperties
          baseProperties.2.1 (type := keyAllocation.1)
          (next := keyAllocation.2) rfl
        let valueAllocation := keyAllocation.2.fresh
        have valueProperties := fresh_eq_inferenceProperties
          keyProperties.2.1 (type := valueAllocation.1)
          (next := valueAllocation.2) rfl
        have baseAtValue : basePlace.type.VariablesBelow
            valueAllocation.2.inference.next :=
          baseProperties.2.2.weaken
            (keyProperties.1.trans valueProperties.1).next_le
        have keyAtValue : keyAllocation.1.VariablesBelow
            valueAllocation.2.inference.next :=
          keyProperties.2.2.weaken valueProperties.1.next_le
        have mappingBelow :
            (Ty.mapping keyAllocation.1 valueAllocation.1).VariablesBelow
              valueAllocation.2.inference.next :=
          (Ty.variablesBelow_mapping_iff _ _ _).2
            ⟨keyAtValue, valueProperties.2.2⟩
        cases unifyResult : unify valueAllocation.2 basePlace.type
            (.mapping keyAllocation.1 valueAllocation.1) with
        | error error =>
            simp [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
        | ok unifiedState =>
            simp only [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
            have unifyProgress := unify_inferenceProgress
              valueProperties.2.1.solved baseAtValue mappingBelow unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              valueProperties.2.1 baseAtValue mappingBelow unifyResult
            have keyAtUnified : keyAllocation.1.VariablesBelow
                unifiedState.inference.next :=
              keyAtValue.weaken unifyProgress.next_le
            have resolvedKeyBelow :
                (unifiedState.resolve keyAllocation.1).VariablesBelow
                  unifiedState.inference.next :=
              unifiedReady.solved.variablesBelow_apply keyAtUnified
            cases keyResult : inferExprFuel fuel context key
                (some (unifiedState.resolve baseState.fresh.1)) unifiedState with
            | error error =>
                simp [keyResult, bind, Except.bind] at success
            | ok keyPair =>
                rcases keyPair with ⟨inferredKey, keyState⟩
                simp only [keyResult, bind, Except.bind, Prod.eta, pure,
                  Pure.pure, Except.pure] at success
                injection success with resultEq
                rw [← resultEq]
                have keyExpressionProperties := keyInduction baseState.fresh.1
                  unifiedState unifiedReady validated canonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    simpa only [keyAllocation] using resolvedKeyBelow)
                  (inferredKey, keyState) keyResult
                have fromValueToKey :=
                  unifyProgress.trans keyExpressionProperties.1
                have resolvedValueBelow :=
                  fromValueToKey.resolve_variablesBelow
                    valueProperties.2.2
                exact ⟨baseProperties.1.trans
                    (keyProperties.1.trans
                      (valueProperties.1.trans fromValueToKey)),
                  keyExpressionProperties.2.1, resolvedValueBelow⟩
  case case69 =>
    simp_all [InferPlaceFuelInferenceProperties, inferPlaceFuel, bind,
      Except.bind]
  case case70 =>
    intros fuel context target operator value initial placeInduction
      valueInduction
    unfold InferAssignedValueFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferAssignedValueFuel at success
    cases placeResult : inferPlaceFuel fuel context target initial with
    | error error =>
        simp [placeResult, bind, Except.bind] at success
    | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeProperties := placeInduction ready validated canonical
        (place, placeState) placeResult
      have finishValue (fittedState : State)
          (fitProgress : placeState.InferenceProgress fittedState)
          (fittedReady : fittedState.InferenceReady) (expected : Ty)
          (expectedBelow : expected.VariablesBelow fittedState.inference.next)
          (valueProperties : InferExprFuelInferenceProperties fuel context
            value (some expected) fittedState)
          (tailSuccess :
            (do
              let (inferredValue, finalState) ← inferExprFuel fuel context
                value (some expected) fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue,
                finalState)) = .ok result) :
          initial.InferenceProgress result.2.2 ∧
            result.2.2.InferenceReady ∧
            result.1.target.type.VariablesBelow
              result.2.2.inference.next ∧
            result.2.1.type.VariablesBelow
              result.2.2.inference.next := by
        cases valueResult : inferExprFuel fuel context value (some expected)
            fittedState with
        | error error =>
            simp [valueResult, bind, Except.bind] at tailSuccess
        | ok valuePair =>
          rcases valuePair with ⟨inferredValue, finalState⟩
          simp only [valueResult, bind, Except.bind, Prod.eta, pure,
            Pure.pure, Except.pure] at tailSuccess
          injection tailSuccess with resultEq
          rw [← resultEq]
          have inferredProperties := valueProperties fittedReady validated
            canonical
            (by
              intro candidate member
              simp only [Option.mem_def] at member
              injection member with typeEq
              subst candidate
              exact expectedBelow)
            (inferredValue, finalState) valueResult
          have throughValue := fitProgress.trans inferredProperties.1
          have targetBelow :=
            throughValue.resolve_variablesBelow placeProperties.2.2
          exact ⟨placeProperties.1.trans throughValue,
            inferredProperties.2.1, targetBelow, inferredProperties.2.2⟩
      have finishNonEqual
          (valueProperties : ∀ fittedState : State,
            InferExprFuelInferenceProperties fuel context value
              (some .word) fittedState)
          (tailSuccess :
            (do
              let fittedState ← unify placeState place.type .word
              let (inferredValue, finalState) ← inferExprFuel fuel context
                value (some .word) fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue,
                finalState)) = .ok result) :
          initial.InferenceProgress result.2.2 ∧
            result.2.2.InferenceReady ∧
            result.1.target.type.VariablesBelow
              result.2.2.inference.next ∧
            result.2.1.type.VariablesBelow
              result.2.2.inference.next := by
        cases unifyResult : unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
          simp only [unifyResult, bind, Except.bind] at tailSuccess
          have fitProgress := unify_inferenceProgress
            placeProperties.2.1.solved placeProperties.2.2
            (Ty.variablesBelow_constructor _ _) unifyResult
          have fittedReady := unify_preserves_inferenceReady
            placeProperties.2.1 placeProperties.2.2
            (Ty.variablesBelow_constructor _ _) unifyResult
          exact finishValue fittedState fitProgress fittedReady .word
            (Ty.variablesBelow_constructor _ _)
            (valueProperties fittedState) tailSuccess
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          exact finishValue placeState
            (State.InferenceProgress.refl placeProperties.2.1.solved)
            placeProperties.2.1 (placeState.resolve place.type)
            (placeProperties.2.1.solved.variablesBelow_apply
              placeProperties.2.2)
            (valueInduction place placeState) success
      | add => exact finishNonEqual (valueInduction place) success
      | subtract => exact finishNonEqual (valueInduction place) success
      | multiply => exact finishNonEqual (valueInduction place) success
      | divide => exact finishNonEqual (valueInduction place) success
      | modulo => exact finishNonEqual (valueInduction place) success
      | bitAnd => exact finishNonEqual (valueInduction place) success
      | bitXor => exact finishNonEqual (valueInduction place) success
      | bitOr => exact finishNonEqual (valueInduction place) success
  case case71 =>
    simp [InferExprsFuelInferenceProperties, inferExprsFuel]
  case case72 =>
    intros context initial fuel
    unfold InferExprsFuelInferenceProperties
    intro ready _ _ result success
    unfold inferExprsFuel at success
    injection success with resultEq
    subst result
    exact ⟨State.InferenceProgress.refl ready.solved, ready, by simp⟩
  case case73 =>
    intros context initial fuel expression rest expressionInduction
      tailInduction
    unfold InferExprsFuelInferenceProperties
    intro ready validated canonical result success
    unfold inferExprsFuel at success
    cases expressionResult : inferExprFuel fuel context expression none
        initial with
    | error error =>
        simp [expressionResult, bind, Except.bind] at success
    | ok expressionPair =>
        rcases expressionPair with ⟨inferred, expressionState⟩
        simp only [expressionResult, bind, Except.bind] at success
        cases tailResult : inferExprsFuel fuel context rest expressionState with
        | error error =>
            simp [tailResult, bind, Except.bind] at success
        | ok tailPair =>
            rcases tailPair with ⟨tail, finalState⟩
            simp only [tailResult, bind, Except.bind] at success
            injection success with resultEq
            subst result
            have expressionProperties := expressionInduction ready validated
              canonical (by simp) (inferred, expressionState)
              expressionResult
            have tailProperties := tailInduction expressionState
              expressionProperties.2.1 validated canonical
              (tail, finalState) tailResult
            refine ⟨expressionProperties.1.trans tailProperties.1,
              tailProperties.2.1, ?_⟩
            intro element member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact expressionProperties.2.2.weaken
                tailProperties.1.next_le
            · exact tailProperties.2.2 element tailMember
  case case74 =>
    simp [InferMatchCasesFuelInferenceProperties, inferMatchCasesFuel]
  case case76 =>
    intros context scrutineeType expectedReturn outerScope initial fuel arm rest
      bodyInduction tailInduction
    unfold InferMatchCasesFuelInferenceProperties
    intro ready validated canonical scrutineeBelow returnBelow scopeEq result
      success
    subst outerScope
    unfold inferMatchCasesFuel at success
    simp only [bind, Except.bind] at success
    cases patternResult : inferMatchPatternFuel fuel context arm.value.pattern
        scrutineeType initial with
    | error error =>
        simp [patternResult, bind, Except.bind] at success
    | ok patternPair =>
        rcases patternPair with ⟨pattern, patternState⟩
        simp only [patternResult, bind, Except.bind] at success
        cases bodyResult : inferStatementsFuel fuel context
            arm.value.body.value expectedReturn patternState with
        | error error =>
            simp [bodyResult, bind, Except.bind] at success
        | ok body =>
            simp only [bodyResult, bind, Except.bind] at success
            cases tailResult : inferMatchCasesFuel fuel context scrutineeType
                expectedReturn initial.lexicalScope rest
                (body.state.restoreLexicalScope initial.lexicalScope) with
            | error error =>
                simp [tailResult, bind, Except.bind] at success
            | ok tail =>
                simp only [tailResult, bind, Except.bind] at success
                injection success with resultEq
                subst result
                have patternProperties :=
                  inferMatchPatternFuel_inferenceProperties ready
                    scrutineeBelow validated patternResult
                have returnAtPattern :=
                  returnBelow.weaken patternProperties.1.next_le
                have bodyProperties := bodyInduction patternState
                  patternProperties.2.1 validated canonical returnAtPattern
                  body bodyResult
                have throughBody :=
                  patternProperties.1.trans bodyProperties.1
                have restoredProperties :=
                  State.restoreLexicalScope_inferenceProperties ready
                    throughBody
                have tailProperties := tailInduction body
                  restoredProperties.2 validated canonical
                  (scrutineeBelow.weaken restoredProperties.1.next_le)
                  (returnBelow.weaken restoredProperties.1.next_le)
                  (by simp) tail tailResult
                exact ⟨restoredProperties.1.trans tailProperties.1,
                  tailProperties.2⟩
  case case75 =>
    intros context scrutineeType expectedReturn outerScope initial fuel
    unfold InferMatchCasesFuelInferenceProperties
    intro ready _ _ _ _ scopeEq result success
    unfold inferMatchCasesFuel at success
    injection success with resultEq
    subst result
    exact ⟨State.InferenceProgress.refl ready.solved, ready, scopeEq⟩

private theorem inferExprFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) :
    InferExprFuelInferenceProperties fuel context expression expected state :=
  inferFuel_inferenceProperties_internal.1 fuel context expression expected state

private theorem inferStatementsFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) :
    InferStatementsFuelInferenceProperties fuel context statements
      expectedReturn state :=
  inferFuel_inferenceProperties_internal.2.2.2.1 fuel context statements
    expectedReturn state

private theorem inferForItemsFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (items : List Syntax.ForItem)
    (state : State) :
    InferForItemsFuelInferenceProperties fuel context items state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.1
    fuel context items state

private theorem inferForItemFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (item : Syntax.ForItem)
    (state : State) :
    InferForItemFuelInferenceProperties fuel context item state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.2.1
    fuel context item state

private theorem inferPlaceFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (target : Syntax.Expr) (state : State) :
    InferPlaceFuelInferenceProperties fuel context target state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.2.2.1
    fuel context target state

private theorem inferAssignedValueFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr) (state : State) :
    InferAssignedValueFuelInferenceProperties fuel context target operator
      value state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.2.2.2.1
    fuel context target operator value state

private theorem inferExprsFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (expressions : List Syntax.Expr)
    (state : State) :
    InferExprsFuelInferenceProperties fuel context expressions state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.2.2.2.2.1
    fuel context expressions state

private theorem inferMatchCasesFuel_inferenceProperties_internal
    (fuel : Nat) (context : Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) :
    InferMatchCasesFuelInferenceProperties fuel context scrutineeType
      expectedReturn outerScope cases state :=
  inferFuel_inferenceProperties_internal.2.2.2.2.2.2.2.2.2.2
    fuel context scrutineeType expectedReturn outerScope cases state

/-- Successful expression inference makes monotone inference progress, leaves
the resulting state ready for further inference, and returns a type whose
variables are allocated by that state. -/
theorem inferExprFuel_inferenceProperties
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact inferExprFuel_inferenceProperties_internal fuel context expression
    expected state ready validated canonical expectedBelow result success

/-- Successful statement-list inference makes monotone inference progress,
leaves the resulting state ready for further inference, and returns a block
type whose variables are allocated by that state. -/
theorem inferStatementsFuel_inferenceProperties
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn
      state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.type.VariablesBelow result.state.inference.next := by
  exact inferStatementsFuel_inferenceProperties_internal fuel context
    statements expectedReturn state ready validated canonical returnBelow
    result success

/-- Successful `for`-item sequence inference makes monotone progress and
leaves the resulting state ready for the condition or loop body. -/
theorem inferForItemsFuel_inferenceProperties
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    state.InferenceProgress result.state ∧ result.state.InferenceReady := by
  exact inferForItemsFuel_inferenceProperties_internal fuel context items state
    ready validated canonical result success

/-- Successful inference of one restricted `for` item makes monotone progress
and preserves inference readiness. -/
theorem inferForItemFuel_inferenceProperties
    {fuel : Nat} {context : Context} {item : Syntax.ForItem} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    state.InferenceProgress result.2 ∧ result.2.InferenceReady := by
  exact inferForItemFuel_inferenceProperties_internal fuel context item state
    ready validated canonical result success

/-- Successful place inference makes monotone inference progress, preserves
readiness, and returns a place type bounded by the resulting allocator. -/
theorem inferPlaceFuel_inferenceProperties
    {fuel : Nat} {context : Context} {target : Syntax.Expr} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  exact inferPlaceFuel_inferenceProperties_internal fuel context target state
    ready validated canonical result success

/-- Successful value-assignment inference makes monotone inference progress,
preserves readiness, and bounds both finalized target and value types. -/
theorem inferAssignedValueFuel_inferenceProperties
    {fuel : Nat} {context : Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    state.InferenceProgress result.2.2 ∧
      result.2.2.InferenceReady ∧
      result.1.target.type.VariablesBelow result.2.2.inference.next ∧
      result.2.1.type.VariablesBelow result.2.2.inference.next := by
  exact inferAssignedValueFuel_inferenceProperties_internal fuel context target
    operator value state ready validated canonical result success

/-- Successful inference of a source-ordered expression list makes monotone
progress, preserves readiness, and bounds every inferred element type. -/
theorem inferExprsFuel_inferenceProperties
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    state.InferenceProgress result.2 ∧
      result.2.InferenceReady ∧
      ∀ expression ∈ result.1,
        expression.type.VariablesBelow result.2.inference.next := by
  exact inferExprsFuel_inferenceProperties_internal fuel context expressions
    state ready validated canonical result success

/-- Successful explicit match-case inference makes monotone progress, remains
ready, and restores the supplied outer lexical scope. -/
theorem inferMatchCasesFuel_inferenceProperties
    {fuel : Nat} {context : Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {cases : List Syntax.MatchCase} {state : State}
    (ready : state.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutineeType.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (scopeEq : state.lexicalScope = outerScope)
    {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    state.InferenceProgress result.state ∧
      result.state.InferenceReady ∧
      result.state.lexicalScope = outerScope := by
  exact inferMatchCasesFuel_inferenceProperties_internal fuel context
    scrutineeType expectedReturn outerScope cases state ready validated
    canonical scrutineeBelow returnBelow scopeEq result success

set_option maxHeartbeats 1000000 in
private theorem inferFuel_preserves_lexicalScope_internal :
    (∀ fuel context expression expected state,
      PreservesLexicalScope Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesLexicalScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesLexicalScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ (_fuel : Nat) (_context : Context)
      (_statements : List Syntax.Statement) (_expectedReturn : Ty)
      (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_statement : Syntax.Statement)
      (_expectedReturn : Ty) (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context)
      (_items : List Syntax.ForItem) (_state : State), True) ∧
    (∀ (_fuel : Nat) (_context : Context) (_item : Syntax.ForItem)
      (_state : State), True) ∧
    (∀ fuel context target state,
      PreservesLexicalScope Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesLexicalScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesLexicalScope Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      RestoresOuterScope MatchCasesResult.state outerScope state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn
          outerScope cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesLexicalScope Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesLexicalScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesLexicalScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun _ _ _ _ _ => True)
    (motive5 := fun _ _ _ _ _ => True)
    (motive6 := fun _ _ _ _ => True)
    (motive7 := fun _ _ _ _ => True)
    (motive8 := fun fuel context target state =>
      PreservesLexicalScope Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesLexicalScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesLexicalScope Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      RestoresOuterScope MatchCasesResult.state outerScope state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn
          outerScope cases state))
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases innerResult : inferExprFuel fuel context inner expected allocated with
    | error error => simp [innerResult, bind, Except.bind] at success
    | ok inferred =>
        simp only [innerResult, bind, Except.bind] at success
        have innerScope := innerInduction inferred innerResult
        have allocationScope :=
          allocateExpressionId_success_lexicalScope allocationEq
        have recordedScope :=
          recordExpressionWithExpected_lexicalScope success
        exact recordedScope.trans (innerScope.trans allocationScope)
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases elementsResult :
        inferExprsFuel fuel context elements.elements allocated with
    | error error => simp [elementsResult, bind, Except.bind] at success
    | ok inferred =>
        simp only [elementsResult, bind, Except.bind] at success
        have elementsScope := elementsInduction inferred elementsResult
        have allocationScope :=
          allocateExpressionId_success_lexicalScope allocationEq
        have recordedScope :=
          recordExpressionWithExpected_lexicalScope success
        exact recordedScope.trans (elementsScope.trans allocationScope)
  case case12 =>
    intros context expression expected initial fuel id allocated allocationEq
      operator operand expressionEq operandInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases operandResult : inferExprFuel fuel context operand none allocated with
    | error error =>
        simp [operandResult, bind, Except.bind] at success
    | ok inferredOperand =>
        have operandScope := operandInduction inferredOperand operandResult
        have allocationScope :=
          allocateExpressionId_success_lexicalScope allocationEq
        have throughOperand := operandScope.trans allocationScope
        simp only [operandResult, bind, Except.bind] at success
        repeat' first | split at success
        all_goals try cases success
        all_goals try have operatorScope :=
          inferUnaryOperator_lexicalScope (by assumption)
        all_goals try have selectionScope :=
          selectFunctionCandidateFrom_lexicalScope (by assumption)
        all_goals try have recordedScope :=
          recordExpressionWithExpected_lexicalScope (by assumption)
        all_goals try
          exact (recordSelectedCall_lexicalScope _ _ _ _ _).trans
            (selectionScope.trans throughOperand)
        all_goals simp_all [State.lexicalScope]
        all_goals grind
  case case13 =>
    intros context expression expected initial fuel id allocated allocationEq
      left operator right expressionEq leftInduction rightInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases leftResult : inferExprFuel fuel context left none allocated with
    | error error =>
        simp [leftResult, bind, Except.bind] at success
    | ok leftPair =>
        rcases leftPair with ⟨inferredLeft, leftState⟩
        simp only [leftResult, bind, Except.bind, Prod.eta] at success
        have leftScope := leftInduction
          (inferredLeft, leftState) leftResult
        cases rightResult : inferExprFuel fuel context right none leftState with
        | error error =>
            simp [rightResult, bind, Except.bind] at success
        | ok rightPair =>
            rcases rightPair with ⟨inferredRight, rightState⟩
            simp only [rightResult, bind, Except.bind, Prod.eta] at success
            have rightScope := rightInduction leftState
              (inferredRight, rightState) rightResult
            have allocationScope :=
              allocateExpressionId_success_lexicalScope allocationEq
            have throughArguments :=
              rightScope.trans (leftScope.trans allocationScope)
            let integerLiterals := relevantIntegerLiterals rightState
              allocated.integerLiterals.length [inferredLeft, inferredRight]
            have finishInferred (inferred : OperatorInferenceResult)
                (inferenceSuccess : inferBinaryOperator context operator.value
                  inferredLeft.type inferredRight.type expected integerLiterals
                    rightState = .ok inferred)
                (recordSuccess : recordExpressionWithExpected context
                  expression id inferred.type
                  (.binary inferredLeft.id operator.value inferredRight.id)
                  inferred.requirements expected inferred.state = .ok result) :
                result.2.lexicalScope = initial.lexicalScope := by
              exact (recordExpressionWithExpected_lexicalScope recordSuccess).trans
                ((inferBinaryOperator_lexicalScope inferenceSuccess).trans
                  throughArguments)
            cases dispatchEq : binaryOperatorDispatch operator.value with
            | traitMethod traitName methodName =>
                simp only [integerLiterals, dispatchEq] at success
                cases inferredResult : inferBinaryOperator context
                    operator.value inferredLeft.type inferredRight.type expected
                    integerLiterals rightState with
                | error error =>
                    simp [integerLiterals, inferredResult, bind, Except.bind]
                      at success
                | ok inferred =>
                    simp only [integerLiterals, inferredResult, bind,
                      Except.bind] at success
                    exact finishInferred inferred inferredResult success
            | function name =>
                simp only [integerLiterals, dispatchEq] at success
                cases functionsResult : functionsNamed context name with
                | error error =>
                    simp [functionsResult, bind, Except.bind] at success
                | ok candidates =>
                    simp only [functionsResult, bind, Except.bind] at success
                    cases candidates with
                    | nil =>
                        cases inferredResult : inferBinaryOperator context
                            operator.value inferredLeft.type inferredRight.type
                            expected integerLiterals rightState with
                        | error error =>
                            simp [integerLiterals, inferredResult, bind,
                              Except.bind] at success
                        | ok inferred =>
                            simp only [integerLiterals, inferredResult, bind,
                              Except.bind] at success
                            exact finishInferred inferred inferredResult success
                    | cons candidate rest =>
                        cases selectionResult : selectFunctionCandidateFrom
                            context name (candidate :: rest)
                            [inferredLeft, inferredRight] integerLiterals id
                            (some .bool) rightState with
                        | error error =>
                            simp [integerLiterals, selectionResult, bind,
                              Except.bind] at success
                        | ok attempt =>
                            simp only [integerLiterals, selectionResult, bind,
                              Except.bind] at success
                            have selectedScope :=
                              selectFunctionCandidateFrom_lexicalScope
                                selectionResult
                            cases fittedResult : withExpected context
                                attempt.state attempt.result expected with
                            | error error =>
                                simp [fittedResult, bind, Except.bind]
                                  at success
                            | ok fitted =>
                                simp only [fittedResult, bind, Except.bind,
                                  pure, Pure.pure, Except.pure] at success
                                have fittedScope :=
                                  withExpected_lexicalScope fittedResult
                                injection success with resultEq
                                subst result
                                exact
                                  recordSelectedCallResult_lexicalScope
                                      expression
                                      { span := operator.span
                                        value := .identifier {
                                          span := operator.span
                                          value := name
                                        } }
                                      name [inferredLeft, inferredRight] attempt
                                      fitted.expression fitted.coercions
                                      fitted.state
                                    |>.trans (fittedScope.trans
                                      (selectedScope.trans throughArguments))
  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq
      conditionInduction thenInduction elseInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition
        (some .bool) allocated with
    | error error =>
        simp [conditionResult, bind, Except.bind] at success
    | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult, bind, Except.bind, Prod.eta] at success
        have conditionScope := conditionInduction
          (inferredCondition, conditionState) conditionResult
        cases thenResult : inferExprFuel fuel context thenBranch expected
            conditionState with
        | error error =>
            simp [thenResult, bind, Except.bind] at success
        | ok thenPair =>
            rcases thenPair with ⟨inferredThen, thenState⟩
            simp only [thenResult, bind, Except.bind, Prod.eta] at success
            have thenScope := thenInduction conditionState
              (inferredThen, thenState) thenResult
            cases elseResult : inferExprFuel fuel context elseBranch expected
                thenState with
            | error error =>
                simp [elseResult, bind, Except.bind] at success
            | ok elsePair =>
                rcases elsePair with ⟨inferredElse, elseState⟩
                simp only [elseResult, bind, Except.bind, Prod.eta] at success
                have elseScope := elseInduction thenState
                  (inferredElse, elseState) elseResult
                cases unifyResult : unify elseState inferredThen.type
                    inferredElse.type with
                | error error =>
                    simp [unifyResult, bind, Except.bind] at success
                | ok unifiedState =>
                    simp only [unifyResult, bind, Except.bind] at success
                    have unifiedScope :=
                      unify_preserves_lexicalScope unifyResult
                    have recordedScope :=
                      recordExpressionWithExpected_lexicalScope success
                    have allocationScope :=
                      allocateExpressionId_success_lexicalScope allocationEq
                    exact recordedScope.trans (unifiedScope.trans
                      (elseScope.trans (thenScope.trans
                        (conditionScope.trans allocationScope))))
  case case16 =>
    intros context expression expected initial fuel id allocated allocationEq
      callee sourceArguments expressionEq constructorInduction
      argumentsInduction calleeInduction
    unfold PreservesLexicalScope at *
    intro result success
    have allocationScope :=
      allocateExpressionId_success_lexicalScope allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidatesResult :
        constructorCalleeCandidates context allocated callee with
    | error error =>
        simp [candidatesResult, bind, Except.bind] at success
    | ok candidates =>
        simp only [candidatesResult, bind, Except.bind] at success
        cases candidates with
        | cons candidate rest =>
            cases rest with
            | cons second tail =>
                simp at success
            | nil =>
                rcases candidate with ⟨dataType, constructor⟩
                let freshResult :=
                  freshDataConstructorInstantiation dataType constructor
                    allocated
                have constructorScope := constructorInduction
                  freshResult.1 freshResult.2 result
                  (by simpa only [freshResult] using success)
                exact constructorScope.trans
                  ((freshDataConstructorInstantiation_preserves_lexicalScope
                    dataType constructor allocated).trans allocationScope)
        | nil =>
            simp only [bind, Except.bind] at success
            split at success
            · cases success
            · next _ missing _ =>
              cases missing with
              | some missing =>
                  rcases missing with ⟨qualifiers, name⟩
                  simp at success
              | none =>
                cases argumentsResult : inferExprsFuel fuel context
                    sourceArguments.elements allocated with
                | error error =>
                    simp [argumentsResult, bind, Except.bind] at success
                | ok argumentsPair =>
                    rcases argumentsPair with ⟨arguments, argumentState⟩
                    simp only [argumentsResult, bind, Except.bind,
                      Prod.eta] at success
                    have argumentsScope := argumentsInduction
                      (arguments, argumentState) argumentsResult
                    have throughArguments :=
                      argumentsScope.trans allocationScope
                    have finishSelected
                        (name : String)
                        (candidates : List ProgramFunctionSignature)
                        (attempt : CandidateAttemptResult)
                        (selectionSuccess :
                          selectFunctionCandidateFrom context name candidates
                            arguments
                            (relevantIntegerLiterals argumentState
                              allocated.integerLiterals.length arguments)
                            id expected argumentState = .ok attempt)
                        (resultEq :
                          recordSelectedCall expression callee name arguments
                            attempt = result) :
                        result.2.lexicalScope = initial.lexicalScope := by
                      have selectedScope :=
                        selectFunctionCandidateFrom_lexicalScope
                          selectionSuccess
                      rw [← resultEq]
                      exact (recordSelectedCall_lexicalScope
                        expression callee name arguments attempt).trans
                          (selectedScope.trans throughArguments)
                    have finishIndirect
                        (calleeResult : InferredExpression)
                        (calleeState : State)
                        (calleeSuccess :
                          inferExprFuel fuel context callee none argumentState =
                            .ok (calleeResult, calleeState))
                        (application : IndirectApplicationResult)
                        (applicationSuccess :
                          applyFunctionType context id calleeResult.type
                            arguments expected calleeState = .ok application)
                        (resultEq :
                          recordIndirectCall expression calleeResult arguments
                            application = result) :
                        result.2.lexicalScope = initial.lexicalScope := by
                      have calleeScope := calleeInduction argumentState
                        (calleeResult, calleeState) calleeSuccess
                      have applicationScope :=
                        applyFunctionType_lexicalScope applicationSuccess
                      rw [← resultEq]
                      exact (recordIndirectCall_lexicalScope expression
                        calleeResult arguments application).trans
                          (applicationScope.trans
                            (calleeScope.trans throughArguments))
                    cases qualifiedEq : calleeQualifiedIdentifier? callee with
                    | some qualified =>
                        rcases qualified with ⟨namespacePath, name⟩
                        simp only [qualifiedEq] at success
                        cases binderEq :
                            argumentState.lookupBinder? namespacePath.head! with
                        | some binder =>
                            simp only [binderEq] at success
                            cases calleeResult : inferExprFuel fuel context callee
                                none argumentState with
                            | error error =>
                                simp [calleeResult, bind, Except.bind] at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult, bind, Except.bind,
                                  Prod.eta] at success
                                cases applicationResult : applyFunctionType
                                    context id inferredCallee.type arguments
                                    expected calleeState with
                                | error error =>
                                    simp [applicationResult, bind, Except.bind]
                                      at success
                                | ok application =>
                                    simp only [applicationResult, bind,
                                      Except.bind, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult application
                                      applicationResult resultEq
                        | none =>
                            simp only [binderEq] at success
                            cases functionsResult : qualifiedFunctionsNamed
                                context namespacePath name with
                            | error error =>
                                simp [functionsResult, bind, Except.bind]
                                  at success
                            | ok candidatesOption =>
                                simp only [functionsResult, bind, Except.bind]
                                  at success
                                cases candidatesOption with
                                | some candidates =>
                                    cases selectionResult :
                                        selectFunctionCandidateFrom context
                                          (String.intercalate "."
                                            (namespacePath ++ [name]))
                                          candidates arguments
                                          (relevantIntegerLiterals
                                            argumentState
                                            allocated.integerLiterals.length
                                            arguments)
                                          id expected argumentState with
                                    | error error =>
                                        simp [selectionResult, bind,
                                          Except.bind] at success
                                    | ok attempt =>
                                        simp only [selectionResult, bind,
                                          Except.bind, pure, Pure.pure,
                                          Except.pure] at success
                                        injection success with resultEq
                                        exact finishSelected
                                          (String.intercalate "."
                                            (namespacePath ++ [name]))
                                          candidates attempt selectionResult
                                          resultEq
                                | none =>
                                    cases calleeResult : inferExprFuel fuel
                                        context callee none argumentState with
                                    | error error =>
                                        simp [calleeResult, bind, Except.bind]
                                          at success
                                    | ok calleePair =>
                                        rcases calleePair with
                                          ⟨inferredCallee, calleeState⟩
                                        simp only [calleeResult, bind,
                                          Except.bind, Prod.eta] at success
                                        cases applicationResult :
                                            applyFunctionType context id
                                              inferredCallee.type arguments
                                              expected calleeState with
                                        | error error =>
                                            simp [applicationResult, bind,
                                              Except.bind] at success
                                        | ok application =>
                                            simp only [applicationResult, bind,
                                              Except.bind, pure, Pure.pure,
                                              Except.pure] at success
                                            injection success with resultEq
                                            exact finishIndirect inferredCallee
                                              calleeState calleeResult
                                              application applicationResult
                                              resultEq
                    | none =>
                        simp only [qualifiedEq] at success
                        cases identifierEq : calleeIdentifier? callee with
                        | none =>
                            simp only [identifierEq] at success
                            cases calleeResult : inferExprFuel fuel context callee
                                none argumentState with
                            | error error =>
                                simp [calleeResult, bind, Except.bind] at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult, bind, Except.bind,
                                  Prod.eta] at success
                                cases applicationResult : applyFunctionType
                                    context id inferredCallee.type arguments
                                    expected calleeState with
                                | error error =>
                                    simp [applicationResult, bind, Except.bind]
                                      at success
                                | ok application =>
                                    simp only [applicationResult, bind,
                                      Except.bind, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult application
                                      applicationResult resultEq
                        | some name =>
                            simp only [identifierEq] at success
                            cases binderEq : argumentState.lookupBinder? name with
                            | some binder =>
                                simp only [binderEq] at success
                                cases calleeResult : inferExprFuel fuel context
                                    callee none argumentState with
                                | error error =>
                                    simp [calleeResult, bind, Except.bind]
                                      at success
                                | ok calleePair =>
                                    rcases calleePair with
                                      ⟨inferredCallee, calleeState⟩
                                    simp only [calleeResult, bind, Except.bind,
                                      Prod.eta] at success
                                    cases applicationResult : applyFunctionType
                                        context id inferredCallee.type arguments
                                        expected calleeState with
                                    | error error =>
                                        simp [applicationResult, bind,
                                          Except.bind] at success
                                    | ok application =>
                                        simp only [applicationResult, bind,
                                          Except.bind, pure, Pure.pure,
                                          Except.pure] at success
                                        injection success with resultEq
                                        exact finishIndirect inferredCallee
                                          calleeState calleeResult application
                                          applicationResult resultEq
                            | none =>
                                simp only [binderEq] at success
                                cases functionsResult : functionsNamed context
                                    name with
                                | error error =>
                                    simp [functionsResult, bind, Except.bind]
                                      at success
                                | ok candidates =>
                                    simp only [functionsResult, bind,
                                      Except.bind] at success
                                    cases candidates with
                                    | nil =>
                                        cases builtinEq :
                                            builtinFunctionNamed? name with
                                        | none =>
                                            simp [builtinEq] at success
                                        | some function =>
                                            simp only [builtinEq] at success
                                            exact
                                              (recordBuiltinFunctionCall_lexicalScope
                                                success).trans throughArguments
                                    | cons candidate rest =>
                                        cases selectionResult :
                                            selectFunctionCandidateFrom context
                                              name (candidate :: rest) arguments
                                              (relevantIntegerLiterals
                                                argumentState
                                                allocated.integerLiterals.length
                                                arguments)
                                              id expected argumentState with
                                        | error error =>
                                            simp [selectionResult, bind,
                                              Except.bind] at success
                                        | ok attempt =>
                                            simp only [selectionResult, bind,
                                              Except.bind, pure, Pure.pure,
                                              Except.pure] at success
                                            injection success with resultEq
                                            exact finishSelected name
                                              (candidate :: rest) attempt
                                              selectionResult resultEq
  -- Mapping index expression.
  case case19 =>
    intros context expression expected initial fuel id allocated allocationEq
      base brackets index expressionEq baseInduction indexInduction
    unfold PreservesLexicalScope at *
    intro result success
    have allocationScope :=
      allocateExpressionId_success_lexicalScope allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases baseResult : inferExprFuel fuel context base none allocated with
    | error error =>
        simp [baseResult, bind, Except.bind] at success
    | ok basePair =>
        rcases basePair with ⟨inferredBase, baseState⟩
        simp only [baseResult, bind, Except.bind, Prod.eta] at success
        have baseScope := baseInduction
          (inferredBase, baseState) baseResult
        let keyAllocation := baseState.fresh
        let valueAllocation := keyAllocation.2.fresh
        have keyScope :
            keyAllocation.2.lexicalScope = baseState.lexicalScope := by
          rfl
        have valueScope :
            valueAllocation.2.lexicalScope = keyAllocation.2.lexicalScope := by
          rfl
        cases unifyResult : unify valueAllocation.2 inferredBase.type
            (.mapping keyAllocation.1 valueAllocation.1) with
        | error error =>
            simp [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
        | ok unifiedState =>
            simp only [keyAllocation, valueAllocation, unifyResult, bind,
              Except.bind] at success
            have unifiedScope :=
              unify_preserves_lexicalScope unifyResult
            cases indexResult : inferExprFuel fuel context index
                (some (unifiedState.resolve baseState.fresh.1))
                unifiedState with
            | error error =>
                simp [indexResult, bind, Except.bind] at success
            | ok indexPair =>
                rcases indexPair with ⟨inferredIndex, indexState⟩
                simp only [indexResult, bind, Except.bind, Prod.eta]
                  at success
                have indexScope := indexInduction baseState.fresh.1
                  unifiedState (inferredIndex, indexState) indexResult
                have recordedScope :=
                  recordExpressionWithExpected_lexicalScope success
                exact recordedScope.trans (indexScope.trans
                  (unifiedScope.trans (valueScope.trans (keyScope.trans
                    (baseScope.trans allocationScope)))))
  -- Field selection or qualified constructor reference.
  case case20 =>
    intros context expression expected initial fuel id allocated allocationEq
      base dot name expressionEq constructorInduction
    unfold PreservesLexicalScope at *
    intro result success
    have allocationScope :=
      allocateExpressionId_success_lexicalScope allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidatesResult :
        constructorCalleeCandidates context allocated expression with
    | error error =>
        simp [candidatesResult, bind, Except.bind] at success
    | ok candidates =>
        simp only [candidatesResult, bind, Except.bind] at success
        cases candidates with
        | nil =>
            simp_all [bind, Except.bind]
            repeat' first | split at success
            all_goals contradiction
        | cons candidate rest =>
            cases rest with
            | cons second tail => simp at success
            | nil =>
                rcases candidate with ⟨dataType, constructor⟩
                let freshResult :=
                  freshDataConstructorInstantiation dataType constructor
                    allocated
                have constructorScope := constructorInduction
                  freshResult.1 freshResult.2 result
                  (by simpa only [freshResult] using success)
                exact constructorScope.trans
                  ((freshDataConstructorInstantiation_preserves_lexicalScope
                    dataType constructor allocated).trans allocationScope)
  -- Assignment-value inference threads place and value inference.
  case case70 =>
    intros fuel context target operator value initial placeInduction
      valueInduction
    unfold PreservesLexicalScope at *
    intro result success
    unfold inferAssignedValueFuel at success
    cases placeResult : inferPlaceFuel fuel context target initial with
    | error error =>
        simp [placeResult, bind, Except.bind] at success
    | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeScope := placeInduction (place, placeState) placeResult
      have finishValue (fittedState : State)
          (fittedScope : fittedState.lexicalScope = placeState.lexicalScope)
          (expected : Ty)
          (valueProperties : PreservesLexicalScope Prod.snd fittedState
            (inferExprFuel fuel context value (some expected) fittedState))
          (tailSuccess :
            (do
              let (inferredValue, finalState) ← inferExprFuel fuel context
                value (some expected) fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue,
                finalState)) = .ok result) :
          result.2.2.lexicalScope = initial.lexicalScope := by
        cases valueResult : inferExprFuel fuel context value (some expected)
            fittedState with
        | error error =>
            simp [valueResult, bind, Except.bind] at tailSuccess
        | ok valuePair =>
          rcases valuePair with ⟨inferredValue, finalState⟩
          simp only [valueResult, bind, Except.bind, Prod.eta, pure,
            Pure.pure, Except.pure] at tailSuccess
          injection tailSuccess with resultEq
          rw [← resultEq]
          exact (valueProperties (inferredValue, finalState) valueResult).trans
            (fittedScope.trans placeScope)
      have finishNonEqual
          (valueProperties : ∀ fittedState : State,
            PreservesLexicalScope Prod.snd fittedState
              (inferExprFuel fuel context value (some .word) fittedState))
          (tailSuccess :
            (do
              let fittedState ← unify placeState place.type .word
              let (inferredValue, finalState) ← inferExprFuel fuel context
                value (some .word) fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue,
                finalState)) = .ok result) :
          result.2.2.lexicalScope = initial.lexicalScope := by
        cases unifyResult : unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
          simp only [unifyResult, bind, Except.bind] at tailSuccess
          exact finishValue fittedState
            (unify_preserves_lexicalScope unifyResult) .word
            (valueProperties fittedState) tailSuccess
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          exact finishValue placeState rfl (placeState.resolve place.type)
            (valueInduction place placeState) success
      | add => exact finishNonEqual (valueInduction place) success
      | subtract => exact finishNonEqual (valueInduction place) success
      | multiply => exact finishNonEqual (valueInduction place) success
      | divide => exact finishNonEqual (valueInduction place) success
      | modulo => exact finishNonEqual (valueInduction place) success
      | bitAnd => exact finishNonEqual (valueInduction place) success
      | bitXor => exact finishNonEqual (valueInduction place) success
      | bitOr => exact finishNonEqual (valueInduction place) success
  -- A grouped place delegates directly to its inner place.
  case case67 =>
    intros
    simp_all only [PreservesLexicalScope, inferPlaceFuel]
    exact fun _ _ => True.intro
  -- The remaining structurally uniform branches are discharged by threading
  -- their recursive scope equalities through state-only helper operations.
  all_goals
    intros
  all_goals try trivial
  all_goals
    simp only [PreservesLexicalScope, RestoresOuterScope] at *
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
      | have ih1Applied := ih1 _ _ _ _ (by assumption); clear ih1
      | have ih1Applied := ih1 _ _ _ (by assumption); clear ih1
      | have ih1Applied := ih1 _ _ (by assumption); clear ih1
      | have ih1Applied := ih1 _ (by assumption); clear ih1
      | have ih1Applied := ih1 _ _ (by simp); clear ih1
      | skip
    all_goals first
      | have ih2Applied := ih2 _ _ _ _ (by assumption); clear ih2
      | have ih2Applied := ih2 _ _ _ (by assumption); clear ih2
      | have ih2Applied := ih2 _ _ (by assumption); clear ih2
      | have ih2Applied := ih2 _ (by assumption); clear ih2
      | have ih2Applied := ih2 _ _ (by simp); clear ih2
      | skip
    all_goals first
      | have ih3Applied := ih3 _ _ _ _ (by assumption); clear ih3
      | have ih3Applied := ih3 _ _ _ (by assumption); clear ih3
      | have ih3Applied := ih3 _ _ (by assumption); clear ih3
      | have ih3Applied := ih3 _ (by assumption); clear ih3
      | have ih3Applied := ih3 _ _ (by simp); clear ih3
      | skip
    all_goals try have allocationScope :=
      allocateExpressionId_success_lexicalScope (by assumption)
    all_goals try have statementAllocationScope :=
      allocateStatementId_success_lexicalScope (by assumption)
    all_goals try have requirementsScope :=
      addRequirementsWithIds_success_lexicalScope (by assumption)
    all_goals try have unifiedScope :=
      unify_preserves_lexicalScope (by assumption)
    all_goals try have recordedProperties :=
      recordExpressionWithExpected_lexicalScope (by assumption)
    all_goals try simp_all [State.lexicalScope, State.fresh,
      State.withLocals, State.allocateBinder, State.allocateHiddenLocal,
      State.restoreLexicalScope, State.recordNode, State.addRequirementWithId,
      State.addRequirementsWithIds, bind, Except.bind]
    all_goals try simp_all [recordExpression]
    all_goals grind

private theorem inferExprFuel_preserves_lexicalScope
    (fuel : Nat) (context : Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) :
    PreservesLexicalScope Prod.snd state
      (inferExprFuel fuel context expression expected state) :=
  inferFuel_preserves_lexicalScope_internal.1 fuel context expression expected
    state

/-- Successful expression inference restores every transient lexical scope
introduced while checking lambdas, match arms, and loop bodies. -/
theorem inferExprFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.2.lexicalScope = state.lexicalScope :=
  inferExprFuel_preserves_lexicalScope fuel context expression expected state
    result success

private theorem inferPlaceFuel_preserves_lexicalScope
    (fuel : Nat) (context : Context) (target : Syntax.Expr) (state : State) :
    PreservesLexicalScope Prod.snd state
      (inferPlaceFuel fuel context target state) :=
  inferFuel_preserves_lexicalScope_internal.2.2.2.2.2.2.2.1
    fuel context target state

/-- Successful place inference preserves the caller's stable lexical scope;
index expressions and other transient traversals cannot leak binders. -/
theorem inferPlaceFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    result.2.lexicalScope = state.lexicalScope :=
  inferPlaceFuel_preserves_lexicalScope fuel context target state result
    success

private theorem inferAssignedValueFuel_preserves_lexicalScope
    (fuel : Nat) (context : Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr) (state : State) :
    PreservesLexicalScope (fun result => result.2.2) state
      (inferAssignedValueFuel fuel context target operator value state) :=
  inferFuel_preserves_lexicalScope_internal.2.2.2.2.2.2.2.2.1
    fuel context target operator value state

/-- Successful value-assignment inference preserves the caller's stable
lexical scope across both place and right-hand-side traversal. -/
theorem inferAssignedValueFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {state final : State}
    {assignment : AssignmentResolution} {inferredValue : InferredExpression}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok (assignment, inferredValue, final)) :
    final.lexicalScope = state.lexicalScope :=
  inferAssignedValueFuel_preserves_lexicalScope fuel context target operator
    value state (assignment, inferredValue, final) success

private theorem inferExprsFuel_preserves_lexicalScope
    (fuel : Nat) (context : Context) (expressions : List Syntax.Expr)
    (state : State) :
    PreservesLexicalScope Prod.snd state
      (inferExprsFuel fuel context expressions state) :=
  inferFuel_preserves_lexicalScope_internal.2.2.2.2.2.2.2.2.2.1
    fuel context expressions state

/-- Successful source-ordered expression-list inference preserves the
caller's stable lexical scope.  This is the public scope boundary used by
multi-scrutinee match inference. -/
theorem inferExprsFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    result.2.lexicalScope = state.lexicalScope :=
  inferExprsFuel_preserves_lexicalScope fuel context expressions state result
    success

private theorem inferMatchCasesFuel_restores_outerScope
    (fuel : Nat) (context : Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) :
    RestoresOuterScope MatchCasesResult.state outerScope state
      (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
        cases state) :=
  inferFuel_preserves_lexicalScope_internal.2.2.2.2.2.2.2.2.2.2
    fuel context scrutineeType expectedReturn outerScope cases state

/-- Successful match-case traversal restores the explicit outer lexical
scope after every arm when that scope is the traversal's entry scope. -/
theorem inferMatchCasesFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {cases : List Syntax.MatchCase} {state : State}
    {result : MatchCasesResult}
    (scopeEq : state.lexicalScope = outerScope)
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    result.state.lexicalScope = outerScope :=
  inferMatchCasesFuel_restores_outerScope fuel context scrutineeType
    expectedReturn outerScope cases state result success scopeEq

private theorem pair_except_nextLocal {ε α β : Type}
    {computation : Except ε (α × β)} {result : α × β}
    {initial : State} {nextLocal : β → Nat}
    (invariant : ∀ value state,
      computation = .ok (value, state) →
        initial.nextLocal ≤ nextLocal state)
    (success : computation = .ok result) :
    initial.nextLocal ≤ nextLocal result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem pair_eq_nextLocal {α : Type}
    {result : α × State} {initial : State}
    (invariant : ∀ value state, result = (value, state) →
      initial.nextLocal ≤ state.nextLocal) :
    initial.nextLocal ≤ result.2.nextLocal := by
  exact invariant result.1 result.2 (Prod.eta result)

private theorem triple_eq_nextLocal {α β : Type}
    {result : α × β × State} {initial : State}
    (invariant : ∀ first second state,
      result = (first, second, state) →
        initial.nextLocal ≤ state.nextLocal) :
    initial.nextLocal ≤ result.2.2.nextLocal := by
  rcases result with ⟨first, second, state⟩
  exact invariant first second state rfl

set_option maxHeartbeats 1000000 in
private theorem inferFuel_advances_nextLocal_internal :
    (∀ fuel context expression expected state,
      AdvancesNextLocal Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      AdvancesNextLocal Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      AdvancesNextLocal Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      AdvancesNextLocal BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      AdvancesNextLocal StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      AdvancesNextLocal InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      AdvancesNextLocal Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      AdvancesNextLocal Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      AdvancesNextLocal (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      AdvancesNextLocal Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      AdvancesNextLocal MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn
          outerScope cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      AdvancesNextLocal Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      AdvancesNextLocal Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      AdvancesNextLocal Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      AdvancesNextLocal BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      AdvancesNextLocal StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      AdvancesNextLocal InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      AdvancesNextLocal Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      AdvancesNextLocal Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      AdvancesNextLocal (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      AdvancesNextLocal Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      AdvancesNextLocal MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn
          outerScope cases state))
  -- Generated case 15 is lambda inference.  Parameter binding and body
  -- inference are the only steps which may advance the local allocator.
  case case15 =>
    intros context expression expected state fuel calleeId stateAfterId
      allocationEq keyword parameters returnType body expressionEq bodyInduction
    unfold AdvancesNextLocal at *
    intro result success
    unfold inferExprFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals try have bodyNext := bodyInduction _ _ _ (by assumption)
    all_goals try have allocationNext :=
      allocateExpressionId_success_nextLocal (by assumption)
    all_goals try have lambdaNext :=
      bindLambdaParameters_nextLocal_le (by assumption)
    all_goals try have unifiedNext :=
      unify_preserves_nextLocal (by assumption)
    all_goals try have recordNext :=
      recordExpressionWithExpected_nextLocal (by assumption)
    all_goals simp_all only [except_pure_eq_ok]
    all_goals simp only [State.restoreLexicalScope_nextLocal] at *
    all_goals try omega
    all_goals grind [State.fresh, unify_preserves_nextLocal]
  -- Generated case 67 is a grouped place and delegates directly.
  case case67 =>
    unfold AdvancesNextLocal at *
    intros
    simp_all only [inferPlaceFuel]
  -- Generated case 70 threads a place through optional operator unification
  -- and then through value inference.
  case case70 =>
    intros fuel context target operator value state placeInduction
      valueInduction
    unfold AdvancesNextLocal at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have placeNext :=
      pair_except_nextLocal placeInduction (by assumption)
    all_goals try have valueNext :=
      pair_except_nextLocal (valueInduction _ _) (by assumption)
    all_goals try have unifiedNext :=
      unify_preserves_nextLocal (by assumption)
    all_goals simp_all [Prod.eta]
    all_goals omega
  -- All remaining generated cases have the same shape: expose successful
  -- recursive calls, apply their monotonicity hypotheses, then discharge
  -- state-only operations with exact nextLocal preservation lemmas.
  all_goals
    intros
    unfold AdvancesNextLocal at *
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
      | specialize ih1 _ _ _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ (by assumption)
      | skip
    all_goals try have unifiedNext :=
      unify_preserves_nextLocal (by assumption)
    all_goals try have recordNext :=
      recordExpressionWithExpected_nextLocal (by assumption)
    all_goals try have lambdaNext :=
      bindLambdaParameters_nextLocal_le (by assumption)
    all_goals try have patternNext :=
      inferMatchPatternFuel_nextLocal_le (by assumption)
    all_goals try have unaryNext :=
      inferUnaryOperator_nextLocal (by assumption)
    all_goals try have binaryNext :=
      inferBinaryOperator_nextLocal (by assumption)
    all_goals try have selectionNext :=
      selectFunctionCandidateFrom_nextLocal (by assumption)
    all_goals try have expectedNext :=
      withExpected_nextLocal (by assumption)
    all_goals try have applicationNext :=
      applyFunctionType_nextLocal (by assumption)
    all_goals try have builtinNext :=
      recordBuiltinFunctionCall_nextLocal (by assumption)
    all_goals first
      | have ih1Next := pair_eq_nextLocal ih1
      | have ih1Next := triple_eq_nextLocal ih1
      | skip
    all_goals first
      | have ih2Next := pair_eq_nextLocal ih2
      | have ih2Next := triple_eq_nextLocal ih2
      | skip
    all_goals first
      | have ih3Next := pair_eq_nextLocal ih3
      | have ih3Next := triple_eq_nextLocal ih3
      | skip
    all_goals try simp_all
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.addRequirementsWithIds, State.allocateBinder,
      State.allocateHiddenLocal, State.restoreLexicalScope, State.recordNode,
      bind, Except.bind]
    all_goals try simp_all only [State.allocateExpressionId_nextLocal,
      State.allocateStatementId_nextLocal]
    all_goals try simp_all [recordExpression]
    all_goals try grind [allocateExpressionId_success_nextLocal,
      allocateStatementId_success_nextLocal, unify_preserves_nextLocal,
      freshDataConstructorInstantiation_preserves_nextLocal,
      freshTypes_preserves_nextLocal]

/-- Successful expression inference monotonically advances the shared
declaration-local identity cutoff. -/
theorem inferExprFuel_nextLocal_le
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    state.nextLocal ≤ result.2.nextLocal :=
  inferFuel_advances_nextLocal_internal.1 fuel context expression expected
    state result success

/-- Successful source-ordered statement inference monotonically advances the
shared declaration-local identity cutoff. -/
theorem inferStatementsFuel_nextLocal_le
    {fuel : Nat} {context : Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn
      state = .ok result) :
    state.nextLocal ≤ result.state.nextLocal :=
  inferFuel_advances_nextLocal_internal.2.2.2.1
    fuel context statements expectedReturn state result success

/-- Successful source-ordered expression-list inference monotonically
advances the shared declaration-local identity cutoff. -/
theorem inferExprsFuel_nextLocal_le
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    state.nextLocal ≤ result.2.nextLocal :=
  inferFuel_advances_nextLocal_internal.2.2.2.2.2.2.2.2.2.1
    fuel context expressions state result success

/-- Expression inference preserves the stable-binder allocation bound: it
restores the caller's visible binders and never moves the shared cutoff
backwards. -/
theorem inferExprFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
      (before := state) (after := result.2) ?_
      (inferExprFuel_nextLocal_le success) below
  exact congrArg LexicalScope.binders
    (inferExprFuel_success_lexicalScope_eq success)

/-- Expression-list inference restores the caller's visible binders while
monotonically advancing the shared local allocator. -/
theorem inferExprsFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
      (before := state) (after := result.2) ?_
      (inferExprsFuel_nextLocal_le success) below
  exact congrArg LexicalScope.binders
    (inferExprsFuel_success_lexicalScope_eq success)

/-- Successful inference of a source-ordered `for`-item sequence never moves
the declaration-local identity cutoff backwards. -/
theorem inferForItemsFuel_nextLocal_le
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    state.nextLocal ≤ result.state.nextLocal :=
  inferFuel_advances_nextLocal_internal.2.2.2.2.2.1
    fuel context items state result success

/-- Successful inference of one restricted `for` item never moves the
declaration-local identity cutoff backwards. -/
theorem inferForItemFuel_nextLocal_le
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    state.nextLocal ≤ result.2.nextLocal :=
  inferFuel_advances_nextLocal_internal.2.2.2.2.2.2.1
    fuel context item state result success

private theorem inferPlaceFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferPlaceFuel fuel context target state = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
      (before := state) (after := result.2) ?_
      (inferFuel_advances_nextLocal_internal.2.2.2.2.2.2.2.1
        fuel context target state result success) below
  exact congrArg LexicalScope.binders
    (inferPlaceFuel_success_lexicalScope_eq success)

private theorem inferAssignedValueFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    result.2.2.LocalBindersBelowNextLocal := by
  apply State.LocalBindersBelowNextLocal.transport
      (before := state) (after := result.2.2) ?_
      (inferFuel_advances_nextLocal_internal.2.2.2.2.2.2.2.2.1
        fuel context target operator value state result success) below
  rcases result with ⟨assignment, inferredValue, final⟩
  exact congrArg LexicalScope.binders
    (inferAssignedValueFuel_success_lexicalScope_eq success)

/-- Successful inference of one restricted `for` item preserves the stable
local-identity bound, including the binder introduced by a header `let`. -/
theorem inferForItemFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferForItemFuel fuel context item state = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  cases fuel with
  | zero => simp [inferForItemFuel] at success
  | succ fuel =>
    unfold inferForItemFuel at success
    cases itemEq : item.value with
    | letDecl name sourceType initializer =>
        simp only [itemEq, bind, Except.bind] at success
        cases sourceType with
        | none =>
            cases initializer with
            | none => simp at success
            | some initializer =>
                cases initializerResult :
                    inferExprFuel fuel context initializer none state with
                | error error =>
                    simp [initializerResult, bind, Except.bind] at success
                | ok initializerPair =>
                    rcases initializerPair with
                      ⟨inferredInitializer, initializerState⟩
                    simp only [initializerResult, bind, Except.bind,
                      Prod.eta, pure, Pure.pure, Except.pure] at success
                    injection success with resultEq
                    rw [← resultEq]
                    apply State.allocateBinder_preserves_localBindersBelowNextLocal
                    exact State.withLocals_preserves_localBindersBelowNextLocal
                      initializerState _
                      (inferExprFuel_preserves_localBindersBelowNextLocal below
                        initializerResult)
        | some sourceType =>
            cases initializer with
            | none =>
                cases sourceTypeResult : resolveSourceType context sourceType with
                | error error =>
                    simp [sourceTypeResult, bind, Except.bind] at success
                | ok resolvedType =>
                    simp only [sourceTypeResult, bind, Except.bind, pure,
                      Pure.pure, Except.pure] at success
                    injection success with resultEq
                    rw [← resultEq]
                    apply State.allocateBinder_preserves_localBindersBelowNextLocal
                    exact State.withLocals_preserves_localBindersBelowNextLocal
                      state _ below
            | some initializer =>
                cases sourceTypeResult : resolveSourceType context sourceType with
                | error error =>
                    simp [sourceTypeResult, bind, Except.bind] at success
                | ok resolvedType =>
                    simp only [sourceTypeResult, bind, Except.bind] at success
                    cases initializerResult : inferExprFuel fuel context
                        initializer (some resolvedType) state with
                    | error error =>
                        simp [initializerResult, bind, Except.bind] at success
                    | ok initializerPair =>
                        rcases initializerPair with
                          ⟨inferredInitializer, initializerState⟩
                        simp only [initializerResult, bind, Except.bind,
                          Prod.eta, pure, Pure.pure, Except.pure] at success
                        injection success with resultEq
                        rw [← resultEq]
                        apply
                          State.allocateBinder_preserves_localBindersBelowNextLocal
                        exact
                          State.withLocals_preserves_localBindersBelowNextLocal
                            initializerState _
                            (inferExprFuel_preserves_localBindersBelowNextLocal
                              below initializerResult)
    | expression expression =>
        simp only [itemEq, bind, Except.bind] at success
        cases expressionResult :
            inferExprFuel fuel context expression none state with
        | error error =>
            simp [expressionResult, bind, Except.bind] at success
        | ok expressionPair =>
            rcases expressionPair with ⟨inferredExpression, expressionState⟩
            simp only [expressionResult, bind, Except.bind, Prod.eta, pure,
              Pure.pure, Except.pure] at success
            injection success with resultEq
            rw [← resultEq]
            exact inferExprFuel_preserves_localBindersBelowNextLocal below
              expressionResult
    | assignValue target operator value =>
        simp only [itemEq, bind, Except.bind] at success
        cases assignmentResult : inferAssignedValueFuel fuel context target
            operator.value value state with
        | error error =>
            simp [assignmentResult, bind, Except.bind] at success
        | ok assignmentTriple =>
            rcases assignmentTriple with
              ⟨assignment, inferredValue, assignmentState⟩
            simp only [assignmentResult, bind, Except.bind, Prod.eta, pure,
              Pure.pure, Except.pure] at success
            injection success with resultEq
            rw [← resultEq]
            exact
              inferAssignedValueFuel_preserves_localBindersBelowNextLocal
                below assignmentResult
    | assignBitNot target operator =>
        simp only [itemEq, bind, Except.bind] at success
        cases placeResult : inferPlaceFuel fuel context target state with
        | error error =>
            simp [placeResult, bind, Except.bind] at success
        | ok placePair =>
            rcases placePair with ⟨place, placeState⟩
            simp only [placeResult, bind, Except.bind, Prod.eta] at success
            cases unifyResult : unify placeState place.type .word with
            | error error =>
                simp [unifyResult, bind, Except.bind] at success
            | ok unifiedState =>
                simp only [unifyResult, bind, Except.bind, pure, Pure.pure,
                  Except.pure] at success
                injection success with resultEq
                rw [← resultEq]
                apply State.LocalBindersBelowNextLocal.transport
                    (before := placeState) (after := unifiedState) ?_
                    (by
                      rw [unify_preserves_nextLocal unifyResult]
                      exact Nat.le_refl _)
                    (inferPlaceFuel_preserves_localBindersBelowNextLocal below
                      placeResult)
                exact congrArg LexicalScope.binders
                  (unify_preserves_lexicalScope unifyResult)

/-- Source-ordered `for`-item traversal preserves the stable local-identity
bound through every header declaration and update. -/
theorem inferForItemsFuel_preserves_localBindersBelowNextLocal
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (below : state.LocalBindersBelowNextLocal)
    (success : inferForItemsFuel fuel context items state = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  induction items generalizing state result with
  | nil =>
      simp only [inferForItemsFuel, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact below
  | cons item items induction =>
      unfold inferForItemsFuel at success
      cases itemResult : inferForItemFuel fuel context item state with
      | error error => simp [itemResult, bind, Except.bind] at success
      | ok itemPair =>
          rcases itemPair with ⟨inferredItem, itemState⟩
          simp only [itemResult, bind, Except.bind] at success
          cases tailResult : inferForItemsFuel fuel context items itemState with
          | error error => simp [tailResult, bind, Except.bind] at success
          | ok tail =>
              simp only [tailResult, bind, Except.bind, pure, Pure.pure,
                Except.pure] at success
              have tailBelow := induction
                (inferForItemFuel_preserves_localBindersBelowNextLocal below
                  itemResult)
                tailResult
              injection success with resultEq
              subst result
              exact tailBelow

set_option maxHeartbeats 500000 in
private theorem inferStatementsFuel_preserves_header_internal :
    (∀ fuel context expression expected state,
      PreservesStateHeader Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesStateHeader Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesStateHeader Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesStateHeader BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesStateHeader StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesStateHeader InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesStateHeader Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesStateHeader Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesStateHeader (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesStateHeader Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesStateHeader MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
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

private theorem inferStatementListFuel_preserves_header_internal
    (fuel : Nat) (context : Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) :
    PreservesStateHeader BlockResult.state state
      (inferStatementsFuel fuel context statements expectedReturn state) :=
  inferStatementsFuel_preserves_header_internal.2.2.2.1 fuel context statements
    expectedReturn state

/-- Successful expression inference preserves the declaration owner and the
original input binders. -/
theorem inferExprFuel_state_header
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.2.header = state.header := by
  exact inferStatementsFuel_preserves_header_internal.1
    fuel context expression expected state result success

@[simp] theorem inferExprFuel_preserves_owner
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.2.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferExprFuel_state_header success)

@[simp] theorem inferExprFuel_preserves_inputs
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    result.2.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferExprFuel_state_header success)

/-- Successful statement-list inference preserves the declaration owner and
the original input binders. -/
theorem inferStatementsFuel_state_header
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.header = state.header := by
  exact inferStatementListFuel_preserves_header_internal fuel context statements
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

/-- Successful `for`-item sequence inference preserves declaration identity
and the original input-binder metadata. -/
theorem inferForItemsFuel_state_header
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    result.state.header = state.header := by
  exact inferStatementsFuel_preserves_header_internal.2.2.2.2.2.1
    fuel context items state result success

@[simp] theorem inferForItemsFuel_preserves_owner
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    result.state.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferForItemsFuel_state_header success)

@[simp] theorem inferForItemsFuel_preserves_inputs
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    result.state.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferForItemsFuel_state_header success)

/-- Successful inference of one restricted `for` item preserves declaration
identity and the original input-binder metadata. -/
theorem inferForItemFuel_state_header
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    result.2.header = state.header := by
  exact inferStatementsFuel_preserves_header_internal.2.2.2.2.2.2.1
    fuel context item state result success

@[simp] theorem inferForItemFuel_preserves_owner
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    result.2.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferForItemFuel_state_header success)

@[simp] theorem inferForItemFuel_preserves_inputs
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    result.2.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferForItemFuel_state_header success)

end Solcore.Frontend.SourceInference.Detail
