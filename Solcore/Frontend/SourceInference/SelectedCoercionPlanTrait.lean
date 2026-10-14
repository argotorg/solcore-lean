import Solcore.Frontend.SourceInference.ExpressionProperties

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.Frontend.SourceInference.Detail.SelectedCoercionPlanTrait
open TypeSystem

private def EdgeCorrect (trait : Resolved.DeclarationId) (edge : CoercionEdge) : Prop :=
  edge.predicate = { trait := .declaration trait, subject := edge.source, arguments := [edge.target] }

private def StepCorrect (trait : Resolved.DeclarationId) (step : PlannedCoercionStep) : Prop :=
  step.predicate = { trait := .declaration trait, subject := step.source, arguments := [step.target] }

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
  · simp only [coercionRuleEdge?, traitMismatch] at success
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
                simp only [unified] at success
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

private theorem programTraitId_bne_eq_true_iff_ne
    (left right : ProgramTraitId) :
    (left != right) = true ↔ left ≠ right := by
  change (!instBEqProgramTraitId.beq left right) = true ↔ left ≠ right
  cases left <;> cases right <;>
    simp [instBEqProgramTraitId.beq]
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

private theorem mapCoercionMethodPredicates_success_correct
    (trait : Resolved.DeclarationId) (profile : Option CoercionMethodProfile) :
    ∀ (input output : List CoercionEdge),
      (∀ (edge : CoercionEdge), edge ∈ input → edge.predicate = {
        trait := .declaration trait
        subject := edge.source
        arguments := [edge.target]
      }) →
      input.mapM (attachCoercionMethodPredicates profile) =
        .ok output →
      ∀ (edge : CoercionEdge), edge ∈ output →
        EdgeCorrect trait edge := by
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
          coercionMethodPredicates profile head.source head.target with
      | error error =>
          simp [List.mapM_cons, attachCoercionMethodPredicates, methodResult,
            bind, Except.bind] at success
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
              · exact inputPredicates head (by simp)
              · exact induction tail
                  (fun candidate candidateMember =>
                    inputPredicates candidate (by simp [candidateMember]))
                  tailResult edge member

private theorem coercionEdges_success_correct
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {edges : List CoercionEdge}
    (success : coercionEdges context state profile trait source =
      .ok edges) :
    ∀ edge, edge ∈ edges →
      EdgeCorrect trait edge := by
  unfold coercionEdges at success
  let input :=
    ((context.signatures.implRules.filterMap
      (coercionRuleEdge? trait source)) ++
      assumptionCoercionEdges context state trait source).eraseDups
  change input.mapM (attachCoercionMethodPredicates profile) =
    .ok edges at success
  exact mapCoercionMethodPredicates_success_correct trait profile
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

private theorem plannedCoercionStep_correct_of_edge
    {trait : Resolved.DeclarationId}
    {edge : CoercionEdge}
    (consistent : EdgeCorrect trait edge) :
    StepCorrect trait {
      source := edge.source
      target := edge.target
      predicate := edge.predicate
      methodPredicates := edge.methodPredicates
    } := consistent

private theorem expandCoercionPath_success_correct
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId}
    {path : CoercionPath} {expansion : CoercionExpansion}
    (pathConsistent : ∀ step, step ∈ path.steps →
      StepCorrect trait step)
    (success : expandCoercionPath context state profile trait path =
      .ok expansion) :
    ∀ candidate, candidate ∈ expansion.paths →
      ∀ step, step ∈ candidate.steps →
        StepCorrect trait step := by
  unfold expandCoercionPath at success
  cases edgesResult :
      coercionEdges context state profile trait path.current with
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
        apply plannedCoercionStep_correct_of_edge
        exact coercionEdges_success_correct edgesResult edge
          (List.mem_filter.mp
            (viableCoercionEdges_viable_subset context state _ edgeMember)).1

private theorem expandCoercionPaths_success_correct
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId}
    {frontier : List CoercionPath} {expansion : CoercionExpansion}
    (frontierConsistent : ∀ path, path ∈ frontier →
      ∀ step, step ∈ path.steps →
        StepCorrect trait step)
    (success : expandCoercionPaths context state profile trait frontier =
      .ok expansion) :
    ∀ path, path ∈ expansion.paths →
      ∀ step, step ∈ path.steps →
        StepCorrect trait step := by
  induction frontier generalizing expansion with
  | nil =>
      simp [expandCoercionPaths, pure, Pure.pure, Except.pure] at success
      subst expansion
      simp
  | cons path rest induction =>
      simp only [expandCoercionPaths] at success
      cases headResult :
          expandCoercionPath context state profile trait path with
      | error error =>
          simp [headResult, bind, Except.bind] at success
      | ok head =>
          cases tailResult :
              expandCoercionPaths context state profile trait rest with
          | error error =>
              simp [headResult, tailResult, bind, Except.bind] at success
          | ok tail =>
              simp [headResult, tailResult, bind, Except.bind, pure,
                Pure.pure, Except.pure] at success
              subst expansion
              intro candidate member
              rw [List.mem_append] at member
              rcases member with headMember | tailMember
              · exact expandCoercionPath_success_correct
                  (frontierConsistent path (by simp)) headResult candidate
                  headMember
              · exact induction
                  (fun candidate candidateMember =>
                    frontierConsistent candidate (by simp [candidateMember]))
                  tailResult candidate tailMember

private theorem selectCoercionPath_success_correct
    {trait : Resolved.DeclarationId}
    {source target : Ty} {paths : List CoercionPath}
    {steps : List PlannedCoercionStep}
    (pathsConsistent : ∀ path, path ∈ paths →
      ∀ step, step ∈ path.steps →
        StepCorrect trait step)
    (success : selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step, step ∈ steps →
      StepCorrect trait step := by
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

private theorem searchCoercionPaths_success_correct
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    {fuel : Nat} {frontier : List CoercionPath}
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (frontierConsistent : ∀ path, path ∈ frontier →
      ∀ step, step ∈ path.steps →
        StepCorrect trait step)
    (success : searchCoercionPaths context state profile trait source
      target fuel frontier blocked = .ok (some steps)) :
    ∀ step, step ∈ steps →
      StepCorrect trait step := by
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
          have nextConsistent :=
            expandCoercionPaths_success_correct
              frontierConsistent expandedResult
          cases selectedResult : selectCoercionPath source target next.paths with
          | error error =>
              simp [selectedResult] at success
          | ok selected =>
              simp only [selectedResult] at success
              cases selected with
              | some selectedSteps =>
                  simp [pure, Pure.pure, Except.pure] at success
                  subst steps
                  exact selectCoercionPath_success_correct
                    nextConsistent selectedResult
              | none =>
                  simp only at success
                  by_cases empty : next.paths.isEmpty = true
                  · simp only [empty, ↓reduceIte] at success
                    exact (finishCoercionSearch_ne_some success).elim
                  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
                      at success
                    exact induction nextConsistent success

private theorem plan_correct
    {context : Context} {state : State} {source target : Ty}
    {trait : Resolved.DeclarationId} {profile : Option CoercionMethodProfile}
    {steps : List PlannedCoercionStep}
    (traitSuccess :
      conventionalTraitWithArity? context "Coerce" 2 = .ok (some trait))
    (profileSuccess :
      coercionMethodProfile? context trait = .ok profile)
    (success : coercionPlan? context state source target = .ok (some steps)) :
    ∀ step, step ∈ steps →
      StepCorrect trait step := by
  unfold coercionPlan? at success
  rw [traitSuccess] at success
  simp only [bind, Except.bind] at success
  rw [profileSuccess] at success
  simp only [ ] at success
  let direct : ProgramPredicate := {
    trait := .declaration trait
    subject := source
    arguments := [target]
  }
  cases methodResult :
      coercionMethodPredicates profile source target with
  | error error =>
      simp [methodResult] at success
  | ok methodPredicates =>
      simp only [methodResult] at success
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
              rfl
          | false =>
              cases searchResult :
                  searchCoercionPaths context state profile trait source
                    target context.coercionDepth [{
                      current := source
                      visited := [source]
                      steps := []
                    }] [] with
              | error error =>
                  simp [direct, viableResult, searchResult,
                    ] at success
              | ok plan =>
                  simp only [direct, viableResult, searchResult,
                    ] at success
                  cases plan with
                  | none =>
                      simp [pure, Pure.pure, Except.pure] at success
                      subst steps
                      intro step member
                      simp only [List.mem_singleton] at member
                      subst step
                      rfl
                  | some searchedSteps =>
                      simp [pure, Pure.pure, Except.pure] at success
                      subst steps
                      exact searchCoercionPaths_success_correct
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

/-- Accepted planning preserves the original conventional trait through every
searched edge, independently of whether a method profile was present. -/
theorem trait_of_accepted
    {context : Context} {state : State} {source target : Ty}
    {plan : List PlannedCoercionStep} {step : PlannedCoercionStep}
    (accepted : coercionPlan? context state source target = .ok (some plan))
    (member : step ∈ plan) :
    ∃ trait, conventionalTraitWithArity? context "Coerce" 2 = .ok (some trait) ∧
      step.predicate.trait = .declaration trait := by
  cases traitResult : conventionalTraitWithArity? context "Coerce" 2 with
  | error error => simp [coercionPlan?, traitResult, bind, Except.bind] at accepted
  | ok result =>
    cases result with
    | none => simp [coercionPlan?, traitResult, bind, Except.bind, pure, Except.pure] at accepted
    | some trait =>
      cases profileResult : coercionMethodProfile? context trait with
      | error error => simp [coercionPlan?, traitResult, profileResult, bind, Except.bind] at accepted
      | ok profile =>
        have correct := plan_correct traitResult profileResult accepted step member
        exact ⟨trait, rfl, congrArg (fun predicate : ProgramPredicate => predicate.trait) correct⟩

end Solcore.Frontend.SourceInference.Detail.SelectedCoercionPlanTrait
