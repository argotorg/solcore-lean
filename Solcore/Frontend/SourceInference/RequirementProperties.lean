import Solcore.Frontend.SourceInference.Types

/-! Small preservation laws for function-local source obligation identities. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

private theorem requirementIds_nodup_of_indices_nodup
    (ids : List RequirementId)
    (indices : (ids.map (fun id => id.index)).Nodup) : ids.Nodup := by
  induction ids with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [List.map_cons] at indices
      rw [List.nodup_cons] at indices ⊢
      refine ⟨?_, induction indices.2⟩
      intro member
      exact indices.1 (List.mem_map.mpr ⟨_, member, rfl⟩)

namespace State

theorem initial_requirementsWellFormed (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) :
    (initial owner locals).RequirementsWellFormed := by
  rfl

theorem addRequirementWithId_preserves_requirementsWellFormed
    (state : State) (predicate : ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirementWithId predicate).2.RequirementsWellFormed := by
  simp only [addRequirementWithId, RequirementsWellFormed, List.map_append,
    List.map_cons, List.map_nil, List.range_succ]
  exact congrArg (· ++ [state.nextRequirement]) wellFormed

theorem addRequirement_preserves_requirementsWellFormed
    (state : State) (predicate : ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirement predicate).RequirementsWellFormed := by
  exact addRequirementWithId_preserves_requirementsWellFormed
    state predicate wellFormed

theorem addRequirementsWithIds_preserves_requirementsWellFormed
    (state : State) (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirementsWithIds predicates).2.RequirementsWellFormed := by
  induction predicates generalizing state with
  | nil =>
      simpa [addRequirementsWithIds] using wellFormed
  | cons predicate rest ih =>
      simp only [addRequirementsWithIds]
      exact ih (state.addRequirementWithId predicate).2
        (addRequirementWithId_preserves_requirementsWellFormed
          state predicate wellFormed)

theorem addRequirements_preserves_requirementsWellFormed
    (state : State) (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirements predicates).RequirementsWellFormed := by
  exact addRequirementsWithIds_preserves_requirementsWellFormed
    state predicates wellFormed

/-- A canonical requirement ledger has no duplicate requirement identities. -/
theorem requirementIds_nodup (state : State)
    (wellFormed : state.RequirementsWellFormed) :
    (state.requirements.map (fun requirement => requirement.id)).Nodup := by
  have indices :
      (state.requirements.map (fun requirement => requirement.id)).map
          (fun id => id.index) =
        List.range state.nextRequirement := by
    simpa [RequirementsWellFormed, List.map_map, Function.comp_def] using
      wellFormed
  have indicesNodup :
      ((state.requirements.map (fun requirement => requirement.id)).map
        (fun id => id.index)).Nodup :=
    indices ▸ List.nodup_range
  exact requirementIds_nodup_of_indices_nodup _ indicesNodup

end State

namespace Detail

theorem solveRequirements_preserves_ids
    (context : Context) (state : State) (requirements : List Requirement)
    (solved : List SolvedRequirement)
    (result : solveRequirements context state requirements = .ok solved) :
    solved.map (·.id) = requirements.map (·.id) := by
  induction requirements generalizing solved with
  | nil =>
      simp only [solveRequirements, Except.ok.injEq] at result
      subst solved
      rfl
  | cons requirement rest ih =>
      cases evidenceResult : solveRequirementEvidence context state
          requirement with
      | error error =>
          simp [solveRequirements, evidenceResult, bind, Except.bind] at result
      | ok evidence =>
          cases tailResult : solveRequirements context state rest with
          | error error =>
              simp [solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at result
          | ok tail =>
              simp [solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at result
              injection result with result
              subst solved
              simp only [List.map_cons, ih tail tailResult]

/-- Solving a canonical inference ledger preserves its global requirement-ID
uniqueness.  This is the executable-to-declarative bridge needed by the source
semantics requirement ledger. -/
theorem solveRequirements_ids_nodup
    (context : Context) (state : State) (solved : List SolvedRequirement)
    (wellFormed : state.RequirementsWellFormed)
    (result : solveRequirements context state state.requirements = .ok solved) :
    (solved.map (fun requirement => requirement.id)).Nodup := by
  apply requirementIds_nodup_of_indices_nodup
  have ids := solveRequirements_preserves_ids context state state.requirements
    solved result
  have indices :
      solved.map (fun requirement => requirement.id.index) =
        List.range state.nextRequirement := by
    calc
      solved.map (fun requirement => requirement.id.index) =
          (solved.map (fun requirement => requirement.id)).map
            (fun id => id.index) := by simp
      _ = (state.requirements.map (fun requirement => requirement.id)).map
            (fun id => id.index) := by rw [ids]
      _ = state.requirements.map (fun requirement => requirement.id.index) := by
            simp
      _ = List.range state.nextRequirement := wellFormed
  simpa [List.map_map] using (indices ▸ List.nodup_range)

end Detail

end Solcore.Frontend.SourceInference
