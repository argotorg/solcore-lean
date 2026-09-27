import Solcore.Frontend.SourceInference.Resolution

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
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).RequirementsWellFormed := by
  rfl

/-- Allocating a fresh type metavariable does not change the requirement
ledger. -/
theorem fresh_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.fresh.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Replacing the compatibility-only local environment does not change the
requirement ledger. -/
theorem withLocals_preserves_requirementsWellFormed
    (state : State) (locals : TypeSystem.Environment)
    (wellFormed : state.RequirementsWellFormed) :
    (state.withLocals locals).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Restoring a lexical scope preserves all globally allocated requirement
identities. -/
theorem restoreLexicalScope_preserves_requirementsWellFormed
    (state : State) (scope : LexicalScope)
    (wellFormed : state.RequirementsWellFormed) :
    (state.restoreLexicalScope scope).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating a visible binder changes only lexical and local-scheme state,
not the canonical requirement ledger. -/
theorem allocateBinder_preserves_requirementsWellFormed
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement)
    (wellFormed : state.RequirementsWellFormed) :
    RequirementsWellFormed
      (state.allocateBinder name scheme span comptime schemeRequirements).2 := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Reserving a hidden local identity does not change the requirement ledger. -/
theorem allocateHiddenLocal_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateHiddenLocal.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating an expression identity does not change the requirement ledger. -/
theorem allocateExpressionId_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateExpressionId.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating a statement identity does not change the requirement ledger. -/
theorem allocateStatementId_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateStatementId.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Recording a typed-source node does not change the requirement ledger. -/
theorem recordNode_preserves_requirementsWellFormed
    (state : State) (node : Node)
    (wellFormed : state.RequirementsWellFormed) :
    (state.recordNode node).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Updating an existing expression node does not change the requirement
ledger. -/
theorem modifyExpressionNode_preserves_requirementsWellFormed
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (wellFormed : state.RequirementsWellFormed) :
    (state.modifyExpressionNode id modify).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Updating an existing statement node does not change the requirement
ledger. -/
theorem modifyStatementNode_preserves_requirementsWellFormed
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (wellFormed : state.RequirementsWellFormed) :
    (state.modifyStatementNode id modify).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Recording direct-call provenance changes no canonical requirement IDs. -/
theorem markDirectCallRequirements_preserves_requirementsWellFormed
    (state : State) (requirements : List RequirementId)
    (wellFormed : state.RequirementsWellFormed) :
    (state.markDirectCallRequirements requirements).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

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

open TypeSystem

/-- Unification changes only the inference substitution and fresh-variable
allocator, so a successful step preserves the canonical requirement ledger. -/
theorem unify_preserves_requirementsWellFormed
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next)
    (wellFormed : state.RequirementsWellFormed) :
    next.RequirementsWellFormed := by
  unfold unify at success
  cases unification : state.inference.unify left right with
  | error error =>
      simp [unification, liftUnification, bind, Except.bind] at success
  | ok inference =>
      simp only [unification, liftUnification, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      change state.RequirementsWellFormed
      exact wellFormed

/-- Committing a chosen coercion path allocates its primary and method
requirements in canonical append order. -/
theorem commitCoercionPlan_preserves_requirementsWellFormed
    (state : State) (plan : List PlannedCoercionStep)
    (wellFormed : state.RequirementsWellFormed) :
    (commitCoercionPlan state plan).2.RequirementsWellFormed := by
  induction plan generalizing state with
  | nil =>
      simpa [commitCoercionPlan] using wellFormed
  | cons step rest induction =>
      cases primaryResult : state.addRequirementWithId step.predicate with
      | mk requirement afterPrimary =>
          have primaryWellFormed : afterPrimary.RequirementsWellFormed := by
            simpa [primaryResult] using
              State.addRequirementWithId_preserves_requirementsWellFormed
                state step.predicate wellFormed
          cases methodResult :
              afterPrimary.addRequirementsWithIds step.methodPredicates with
          | mk methodRequirements afterMethods =>
              have methodsWellFormed :
                  afterMethods.RequirementsWellFormed := by
                simpa [methodResult] using
                  State.addRequirementsWithIds_preserves_requirementsWellFormed
                    afterPrimary step.methodPredicates primaryWellFormed
              simpa [commitCoercionPlan, primaryResult, methodResult] using
                induction afterMethods methodsWellFormed

/-- Successful expected-type fitting preserves the canonical requirement
ledger, including the coercion path allocated by its mismatch fallback. -/
theorem withExpected_preserves_requirementsWellFormed
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      change state.RequirementsWellFormed
      exact wellFormed
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          change state.RequirementsWellFormed
          exact wellFormed
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
              | ok plan? =>
                  cases plan? with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact commitCoercionPlan_preserves_requirementsWellFormed
                        state plan wellFormed

/-- A retained expected-type candidate has the same well-formed requirement
ledger as its input state. -/
theorem candidateWithExpected_preserves_requirementsWellFormed
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result))
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_preserves_requirementsWellFormed fittedResult wellFormed

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
