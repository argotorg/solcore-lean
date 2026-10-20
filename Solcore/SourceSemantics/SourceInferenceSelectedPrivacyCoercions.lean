import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContinuation

/-! The coercion search derives private obligations from its actual source,
ground intermediate types, and the selected closed method catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem safe_of_freeVariables_nil {protectedVars : List TypeVarId}
    {state : State} {type : Ty} (closed : type.freeVariables = []) :
    Safe protectedVars state type :=
  safe_closed _ _ (by intro metavariable occurs; simp [closed] at occurs)

private theorem predicate_formed_private {protectedVars : List TypeVarId}
    {state : State} {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) :
    PredicateSafe protectedVars state predicate := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_of_freeVariables_nil
      (StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed.subject)
  · exact safe_of_freeVariables_nil
      (StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil (formed.arguments _ member))

private theorem predicate_parameters_private {protectedVars : List TypeVarId}
    {state : State} {predicate : ProgramPredicate} {substitution : ParameterSubstitution}
    (original : PredicateSafe protectedVars state predicate)
    (range : ∀ parameter replacement, (parameter,replacement) ∈ substitution →
      Safe protectedVars state replacement) :
    PredicateSafe protectedVars state (predicate.applyParameters substitution) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_parameterApply range (original _ (by simp))
  · obtain ⟨originalType, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_parameterApply range (original _ (by simp [originalMember]))

private theorem profile_private {protectedVars : List TypeVarId}
    {state : State} {context : SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (accepted : Detail.coercionMethodProfile? context trait = .ok (some profile)) :
    ∀ predicate ∈ profile.method.wherePredicates, PredicateSafe protectedVars state predicate := by
  unfold Detail.coercionMethodProfile? at accepted
  cases found : context.signatures.trait? trait with
  | none => simp [found, bind, Except.bind] at accepted
  | some signature =>
    simp only [found, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    have signatureMember : signature ∈ context.signatures.traits :=
      List.mem_of_find?_eq_some found
    split at accepted
    · cases methods : signature.methods.filter (fun method => method.name == "coerce") with
      | nil => simp [methods] at accepted
      | cons method rest =>
        cases rest with
        | cons second rest => simp [methods] at accepted
        | nil =>
          simp only [methods, Except.ok.injEq, Option.some.injEq] at accepted
          cases accepted
          have methodMember : method ∈ signature.methods :=
            (List.mem_filter.mp (show method ∈ signature.methods.filter
              (fun method => method.name == "coerce") by rw [methods]; simp)).1
          intro predicate member
          exact predicate_formed_private
            (((catalog.traits_semantic signature signatureMember).methods method methodMember).predicates
              predicate member)
    · simp_all

private theorem methodPredicates_private {protectedVars : List TypeVarId}
    {state : State} {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (sourceSafe : Safe protectedVars state source)
    (targetSafe : Safe protectedVars state target)
    (accepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateSafe protectedVars state predicate := by
  cases profile with
  | none => simp [Detail.coercionMethodPredicates] at accepted; subst predicates; simp
  | some profile =>
    simp only [Detail.coercionMethodPredicates] at accepted
    split at accepted
    · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      subst predicates
      intro predicate member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      apply predicate_parameters_private (profileSafe profile (by simp) original originalMember)
      intro parameter replacement member
      have choice := (List.of_mem_zip member).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at choice
      rcases choice with rfl | rfl
      · exact sourceSafe
      · exact targetSafe
    · simp [throw, Functor.map, Except.map] at accepted

private def EdgeSafe (protectedVars : List TypeVarId) (state : State)
    (edge : Detail.CoercionEdge) : Prop :=
  Safe protectedVars state edge.source ∧ Safe protectedVars state edge.target ∧
    PredicateSafe protectedVars state edge.predicate

private theorem ground_private {protectedVars : List TypeVarId} {state : State} {type : Ty}
    (ground : Detail.isGroundCoercionTarget type = true) : Safe protectedVars state type := by
  simp only [Detail.isGroundCoercionTarget, Bool.and_eq_true] at ground
  have closed : type.freeVariables = [] := by simpa using ground.1
  exact safe_of_freeVariables_nil closed

private theorem coercionRuleEdge_private {protectedVars : List TypeVarId} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {rule : ProgramImplRule}
    {edge : Detail.CoercionEdge}
    (sourceSafe : Safe protectedVars state source)
    (accepted : Detail.coercionRuleEdge? trait source rule = some edge) :
    EdgeSafe protectedVars state edge := by
  by_cases traitMismatch : (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [Detail.coercionRuleEdge?, traitMismatch] at accepted
  · simp only [Detail.coercionRuleEdge?, traitMismatch] at accepted
    cases arguments : (TypedTraitResolution.freshenRuleFor rule {
        trait := ProgramTraitId.declaration trait, subject := source, arguments := [source]
      }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at accepted
    | cons target rest =>
      cases rest with
      | cons second tail => simp [arguments, bind, Option.bind] at accepted
      | nil =>
        simp only [arguments, bind, Option.bind] at accepted
        cases unified : (Unification.unify [{
            left := (TypedTraitResolution.freshenRuleFor rule {
              trait := ProgramTraitId.declaration trait, subject := source, arguments := [source]
            }).head.subject
            right := source
          }]).toOption with
        | none => simp [unified] at accepted
        | some substitution =>
          simp only [unified] at accepted
          by_cases blocked : substitution.domain.any source.freeVariables.contains = true
          · simp [blocked] at accepted
          · by_cases ground : Detail.isGroundCoercionTarget (substitution.apply target) = true
            · simp [blocked, ground] at accepted
              subst edge
              have targetSafe : Safe protectedVars state (substitution.apply target) := ground_private ground
              refine ⟨sourceSafe, targetSafe, ?_⟩
              intro type member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact sourceSafe
              · exact targetSafe
            · simp [blocked, ground] at accepted


private theorem assumptionEdges_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {trait : Resolved.DeclarationId} {source : Ty}
    {edge : Detail.CoercionEdge} (sourceSafe : Safe protectedVars state source)
    (member : edge ∈ Detail.assumptionCoercionEdges context state trait source) :
    EdgeSafe protectedVars state edge := by
  unfold Detail.assumptionCoercionEdges at member
  obtain ⟨assumption, _, produced⟩ := List.mem_filterMap.mp member
  dsimp only at produced
  split at produced
  · cases produced
  · rename_i matching
    have subject : (Detail.applyPredicate state assumption).subject = source := by
      simp only [Bool.or_eq_true, bne_iff_ne, not_or] at matching
      exact Classical.not_not.mp matching.2
    split at produced
    · rename_i target arguments
      split at produced
      · rename_i ground
        cases Option.some.inj produced
        have targetSafe : Safe protectedVars state target := ground_private ground
        refine ⟨sourceSafe, targetSafe, ?_⟩
        intro type member
        rw [subject, arguments] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact sourceSafe
        · exact targetSafe
      · cases produced
    · cases produced

private def FullEdgeSafe (protectedVars : List TypeVarId) (state : State)
    (edge : Detail.CoercionEdge) : Prop :=
  EdgeSafe protectedVars state edge ∧
    ∀ predicate ∈ edge.methodPredicates, PredicateSafe protectedVars state predicate

private theorem attachMethods_private {protectedVars : List TypeVarId} {state : State}
    {profile : Option Detail.CoercionMethodProfile}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (edges : List Detail.CoercionEdge)
    (rawSafe : ∀ edge ∈ edges, EdgeSafe protectedVars state edge)
    {results : List Detail.CoercionEdge}
    (accepted : edges.mapM (fun edge => do
      let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
      pure { edge with methodPredicates }) = Except.ok results) :
    ∀ edge ∈ results, FullEdgeSafe protectedVars state edge := by
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
        · have raw := rawSafe head (by simp)
          exact ⟨raw, methodPredicates_private profileSafe raw.1 raw.2.1 methods⟩
        · exact ih (fun edge member => rawSafe edge (by simp [member])) tails edge member

private theorem coercionEdges_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty} {edges : List Detail.CoercionEdge}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (sourceSafe : Safe protectedVars state source)
    (accepted : Detail.coercionEdges context state profile trait source = .ok edges) :
    ∀ edge ∈ edges, FullEdgeSafe protectedVars state edge := by
  apply attachMethods_private profileSafe _ _ accepted
  intro edge member
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with rules | assumptions
  · obtain ⟨rule, _, produced⟩ := List.mem_filterMap.mp rules
    exact coercionRuleEdge_private sourceSafe produced
  · exact assumptionEdges_private sourceSafe assumptions


def PlannedStepSafe (protectedVars : List TypeVarId) (state : State)
    (step : Detail.PlannedCoercionStep) : Prop :=
  Safe protectedVars state step.source ∧ Safe protectedVars state step.target ∧
    PredicateSafe protectedVars state step.predicate ∧
    ∀ predicate ∈ step.methodPredicates, PredicateSafe protectedVars state predicate

private def PathSafe (protectedVars : List TypeVarId) (state : State)
    (path : Detail.CoercionPath) : Prop :=
  Safe protectedVars state path.current ∧ ∀ step ∈ path.steps, PlannedStepSafe protectedVars state step

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

private theorem expandPath_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {path : Detail.CoercionPath}
    {result : Detail.CoercionExpansion}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (pathSafe : PathSafe protectedVars state path)
    (accepted : Detail.expandCoercionPath context state profile trait path = .ok result) :
    ∀ next ∈ result.paths, PathSafe protectedVars state next := by
  unfold Detail.expandCoercionPath at accepted
  cases edges : Detail.coercionEdges context state profile trait path.current with
  | error error => simp [edges, bind, Except.bind] at accepted
  | ok candidates =>
    simp only [edges, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro next member
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
    have safe := coercionEdges_private profileSafe pathSafe.1 edges edge
      (List.mem_filter.mp (viable_member _ edgeMember)).1
    refine ⟨safe.1.2.1, ?_⟩
    intro step stepMember
    rcases List.mem_append.mp stepMember with old | fresh
    · exact pathSafe.2 step old
    · cases List.mem_singleton.mp fresh
      exact ⟨safe.1.1, safe.1.2.1, safe.1.2.2, safe.2⟩

private theorem expandPaths_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} (paths : List Detail.CoercionPath)
    {result : Detail.CoercionExpansion}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (pathsSafe : ∀ path ∈ paths, PathSafe protectedVars state path)
    (accepted : Detail.expandCoercionPaths context state profile trait paths = .ok result) :
    ∀ next ∈ result.paths, PathSafe protectedVars state next := by
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
        · exact expandPath_private profileSafe (pathsSafe _ (by simp)) headResult _ firstMember
        · exact ih (fun path member => pathsSafe path (by simp [member])) tailResult _ restMember

private theorem selectPath_private {protectedVars : List TypeVarId} {state : State}
    {source target : Ty} {paths : List Detail.CoercionPath}
    {steps : List Detail.PlannedCoercionStep}
    (pathsSafe : ∀ path ∈ paths, PathSafe protectedVars state path)
    (accepted : Detail.selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
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
      exact (pathsSafe path member).2

private theorem finish_not_some {blocked : List Error} {steps : List Detail.PlannedCoercionStep}
    (accepted : Detail.finishCoercionSearch blocked = .ok (some steps)) : False := by
  cases blocked <;> simp [Detail.finishCoercionSearch] at accepted

private theorem searchPaths_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    (fuel : Nat) {frontier : List Detail.CoercionPath} {blocked : List Error}
    {steps : List Detail.PlannedCoercionStep}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (frontierSafe : ∀ path ∈ frontier, PathSafe protectedVars state path)
    (accepted : Detail.searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
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
      have nextSafe := expandPaths_private frontier profileSafe frontierSafe expanded
      cases selected : Detail.selectCoercionPath source target next.paths with
      | error error => simp [selected] at accepted
      | ok option =>
        cases option with
        | some chosen =>
          simp only [selected, pure, Pure.pure, Except.pure,
            Except.ok.injEq, Option.some.injEq] at accepted
          subst steps
          exact selectPath_private nextSafe selected
        | none =>
          simp only [selected] at accepted
          split at accepted
          · exact (finish_not_some accepted).elim
          · exact ih nextSafe accepted


/-- Every obligation in a successful search is private. This follows the
actual direct/search/fallback choice and permits legacy profiles without a
named method. No solver entailment is used as a type-formation premise. -/
theorem coercionPlan_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {source target : Ty}
    {steps : List Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (sourceSafe : Safe protectedVars state source)
    (targetSafe : Safe protectedVars state target)
    (accepted : Detail.coercionPlan? context state source target = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
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
        have profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
            PredicateSafe protectedVars state predicate := by
          intro value member
          have equal : profile = some value := Option.mem_def.mp member
          rw [equal] at profileResult
          exact profile_private catalog profileResult
        cases methodResult : Detail.coercionMethodPredicates profile source target with
        | error error => simp [methodResult] at accepted
        | ok methods =>
          simp only [methodResult] at accepted
          have methodsSafe := methodPredicates_private profileSafe sourceSafe targetSafe methodResult
          let direct : ProgramPredicate := {trait, subject := source, arguments := [target]}
          let directStep : Detail.PlannedCoercionStep := {
            source, target, predicate := direct, methodPredicates := methods
          }
          have directSafe : PlannedStepSafe protectedVars state directStep := by
            refine ⟨sourceSafe, targetSafe, ?_, methodsSafe⟩
            intro type member
            simp only [directStep, direct, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact sourceSafe
            · exact targetSafe
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
              exact directSafe
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
                  exact directSafe
                | some chosen =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  apply searchPaths_private _ profileSafe _ searched
                  intro path member
                  cases List.mem_singleton.mp member
                  exact ⟨sourceSafe, by simp⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
