import Solcore.Frontend.SourceInference.Types

/-! Small preservation laws for function-local source obligation identities. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

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

end Detail

end Solcore.Frontend.SourceInference
