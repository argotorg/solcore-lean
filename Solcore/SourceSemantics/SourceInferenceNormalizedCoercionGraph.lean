import Solcore.SourceSemantics.SourceInferenceNormalizedCoercionTargets
import Solcore.SourceSemantics.SourceInferenceCoercionGraphFormation

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
