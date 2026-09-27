import Solcore.Frontend.SourceInference.Expression

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

/-- Allocating a fresh type metavariable does not remove requirement rows. -/
theorem fresh_requirements_subset (state : State) :
    state.requirements ⊆ state.fresh.2.requirements := by
  exact fun _ member => member

/-- Replacing the compatibility-only local environment does not change the
requirement ledger. -/
theorem withLocals_preserves_requirementsWellFormed
    (state : State) (locals : TypeSystem.Environment)
    (wellFormed : state.RequirementsWellFormed) :
    (state.withLocals locals).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Replacing compatibility-only locals does not remove requirement rows. -/
theorem withLocals_requirements_subset
    (state : State) (locals : TypeSystem.Environment) :
    state.requirements ⊆ (state.withLocals locals).requirements := by
  exact fun _ member => member

/-- Restoring a lexical scope preserves all globally allocated requirement
identities. -/
theorem restoreLexicalScope_preserves_requirementsWellFormed
    (state : State) (scope : LexicalScope)
    (wellFormed : state.RequirementsWellFormed) :
    (state.restoreLexicalScope scope).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Restoring lexical scope does not remove globally allocated requirements. -/
theorem restoreLexicalScope_requirements_subset
    (state : State) (scope : LexicalScope) :
    state.requirements ⊆
      (state.restoreLexicalScope scope).requirements := by
  exact fun _ member => member

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

/-- Allocating a binder does not remove requirement rows. -/
theorem allocateBinder_requirements_subset
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement) :
    state.requirements ⊆
      (state.allocateBinder name scheme span comptime
        schemeRequirements).2.requirements := by
  exact fun _ member => member

/-- Reserving a hidden local identity does not change the requirement ledger. -/
theorem allocateHiddenLocal_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateHiddenLocal.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating a hidden local does not remove requirement rows. -/
theorem allocateHiddenLocal_requirements_subset (state : State) :
    state.requirements ⊆ state.allocateHiddenLocal.2.requirements := by
  exact fun _ member => member

/-- Allocating an expression identity does not change the requirement ledger. -/
theorem allocateExpressionId_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateExpressionId.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating an expression identity does not remove requirement rows. -/
theorem allocateExpressionId_requirements_subset (state : State) :
    state.requirements ⊆ state.allocateExpressionId.2.requirements := by
  exact fun _ member => member

/-- Allocating a statement identity does not change the requirement ledger. -/
theorem allocateStatementId_preserves_requirementsWellFormed
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    state.allocateStatementId.2.RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Allocating a statement identity does not remove requirement rows. -/
theorem allocateStatementId_requirements_subset (state : State) :
    state.requirements ⊆ state.allocateStatementId.2.requirements := by
  exact fun _ member => member

/-- Recording a typed-source node does not change the requirement ledger. -/
theorem recordNode_preserves_requirementsWellFormed
    (state : State) (node : Node)
    (wellFormed : state.RequirementsWellFormed) :
    (state.recordNode node).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Recording a typed-source node does not remove requirement rows. -/
theorem recordNode_requirements_subset (state : State) (node : Node) :
    state.requirements ⊆ (state.recordNode node).requirements := by
  exact fun _ member => member

/-- Updating an existing expression node does not change the requirement
ledger. -/
theorem modifyExpressionNode_preserves_requirementsWellFormed
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (wellFormed : state.RequirementsWellFormed) :
    (state.modifyExpressionNode id modify).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Updating an expression node does not remove requirement rows. -/
theorem modifyExpressionNode_requirements_subset
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    state.requirements ⊆
      (state.modifyExpressionNode id modify).requirements := by
  exact fun _ member => member

/-- Updating an existing statement node does not change the requirement
ledger. -/
theorem modifyStatementNode_preserves_requirementsWellFormed
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (wellFormed : state.RequirementsWellFormed) :
    (state.modifyStatementNode id modify).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Updating a statement node does not remove requirement rows. -/
theorem modifyStatementNode_requirements_subset
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    state.requirements ⊆
      (state.modifyStatementNode id modify).requirements := by
  exact fun _ member => member

/-- Recording direct-call provenance changes no canonical requirement IDs. -/
theorem markDirectCallRequirements_preserves_requirementsWellFormed
    (state : State) (requirements : List RequirementId)
    (wellFormed : state.RequirementsWellFormed) :
    (state.markDirectCallRequirements requirements).RequirementsWellFormed := by
  change state.RequirementsWellFormed
  exact wellFormed

/-- Marking direct-call provenance does not remove requirement rows. -/
theorem markDirectCallRequirements_requirements_subset
    (state : State) (requirements : List RequirementId) :
    state.requirements ⊆
      (state.markDirectCallRequirements requirements).requirements := by
  exact fun _ member => member

theorem addRequirementWithId_preserves_requirementsWellFormed
    (state : State) (predicate : ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirementWithId predicate).2.RequirementsWellFormed := by
  simp only [addRequirementWithId, RequirementsWellFormed, List.map_append,
    List.map_cons, List.map_nil, List.range_succ]
  exact congrArg (· ++ [state.nextRequirement]) wellFormed

/-- Allocating one requirement appends a row to the existing ledger. -/
theorem addRequirementWithId_requirements_subset
    (state : State) (predicate : ProgramPredicate) :
    state.requirements ⊆
      (state.addRequirementWithId predicate).2.requirements := by
  intro requirement member
  simp only [addRequirementWithId, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false]
  exact Or.inl member

theorem addRequirement_preserves_requirementsWellFormed
    (state : State) (predicate : ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirement predicate).RequirementsWellFormed := by
  exact addRequirementWithId_preserves_requirementsWellFormed
    state predicate wellFormed

/-- Allocating one anonymous requirement appends a row to the ledger. -/
theorem addRequirement_requirements_subset
    (state : State) (predicate : ProgramPredicate) :
    state.requirements ⊆ (state.addRequirement predicate).requirements := by
  exact addRequirementWithId_requirements_subset state predicate

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

/-- Allocating a predicate list appends rows without removing the input
ledger. -/
theorem addRequirementsWithIds_requirements_subset
    (state : State) (predicates : List ProgramPredicate) :
    state.requirements ⊆
      (state.addRequirementsWithIds predicates).2.requirements := by
  induction predicates generalizing state with
  | nil => exact fun _ member => member
  | cons predicate rest induction =>
      simp only [addRequirementsWithIds]
      exact List.Subset.trans
        (addRequirementWithId_requirements_subset state predicate)
        (induction (state.addRequirementWithId predicate).2)

theorem addRequirements_preserves_requirementsWellFormed
    (state : State) (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    (state.addRequirements predicates).RequirementsWellFormed := by
  exact addRequirementsWithIds_preserves_requirementsWellFormed
    state predicates wellFormed

/-- Allocating anonymous requirements appends rows without removing the input
ledger. -/
theorem addRequirements_requirements_subset
    (state : State) (predicates : List ProgramPredicate) :
    state.requirements ⊆
      (state.addRequirements predicates).requirements := by
  exact addRequirementsWithIds_requirements_subset state predicates

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

/-- Ordered requirement identities that point to the corresponding predicate
rows of one final inference ledger. -/
inductive RequirementPredicatesCorrespond (requirements : List Requirement) :
    List ProgramPredicate → List RequirementId → Prop where
  | nil : RequirementPredicatesCorrespond requirements [] []
  | cons {predicate id predicates ids}
      (head : ({ id, predicate } : Requirement) ∈ requirements)
      (tail : RequirementPredicatesCorrespond requirements predicates ids) :
      RequirementPredicatesCorrespond requirements
        (predicate :: predicates) (id :: ids)

namespace RequirementPredicatesCorrespond

/-- Ledger extension preserves every established predicate/identity
correspondence. -/
theorem mono {smaller larger : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (included : smaller ⊆ larger)
    (corresponds : RequirementPredicatesCorrespond smaller predicates ids) :
    RequirementPredicatesCorrespond larger predicates ids := by
  induction corresponds with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (included head) induction

end RequirementPredicatesCorrespond

namespace Detail.PlannedCoercionStep

/-- One committed coercion step retains the selected edge and gives every
predicate owned by that edge a stable row in the final requirement ledger. -/
structure CommitCorresponds (requirements : List Requirement)
    (planned : PlannedCoercionStep) (committed : CoercionStep) : Prop where
  source_eq : committed.source = planned.source
  target_eq : committed.target = planned.target
  primary_mem :
    ({ id := committed.requirement, predicate := planned.predicate } :
      Requirement) ∈ requirements
  methods : RequirementPredicatesCorrespond requirements
    planned.methodPredicates committed.methodRequirements

namespace CommitCorresponds

/-- Extending the final ledger preserves one committed-edge correspondence. -/
theorem mono {smaller larger : List Requirement}
    {planned : PlannedCoercionStep} {committed : CoercionStep}
    (included : smaller ⊆ larger)
    (corresponds : CommitCorresponds smaller planned committed) :
    CommitCorresponds larger planned committed := {
  source_eq := corresponds.source_eq
  target_eq := corresponds.target_eq
  primary_mem := included corresponds.primary_mem
  methods := corresponds.methods.mono included
}

end CommitCorresponds

/-- Predicates allocated by one selected edge, in their ledger order. -/
def predicates (step : PlannedCoercionStep) : List ProgramPredicate :=
  step.predicate :: step.methodPredicates

end Detail.PlannedCoercionStep

namespace Detail

/-- The committed coercion spine has exactly one output step for each planned
edge, in the same order, and every output step points into the final ledger. -/
inductive CoercionPlanCommitCorresponds (requirements : List Requirement) :
    List PlannedCoercionStep → List CoercionStep → Prop where
  | nil : CoercionPlanCommitCorresponds requirements [] []
  | cons {planned committed plan steps}
      (head : PlannedCoercionStep.CommitCorresponds requirements
        planned committed)
      (tail : CoercionPlanCommitCorresponds requirements plan steps) :
      CoercionPlanCommitCorresponds requirements
        (planned :: plan) (committed :: steps)

namespace CoercionPlanCommitCorresponds

/-- Extending the final ledger preserves every committed edge and its ordered
requirement correspondence. -/
theorem mono {smaller larger : List Requirement}
    {plan : List PlannedCoercionStep} {steps : List CoercionStep}
    (included : smaller ⊆ larger)
    (corresponds : CoercionPlanCommitCorresponds smaller plan steps) :
    CoercionPlanCommitCorresponds larger plan steps := by
  induction corresponds with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.mono included) induction

/-- Exact commit correspondence transports endpoint and adjacency validity
from the planned path to the retained path, independently of which later
requirement ledger contains the referenced identities. -/
theorem isValid
    {requirements : List Requirement}
    {source target : TypeSystem.Ty}
    {plan : List PlannedCoercionStep} {steps : List CoercionStep}
    (corresponds : CoercionPlanCommitCorresponds requirements plan steps)
    (valid : PlannedCoercionPath.isValid source target plan = true) :
    CoercionPath.isValid source target steps = true := by
  induction corresponds generalizing source with
  | nil =>
      exact valid
  | @cons planned committed plan steps head tail induction =>
      cases tail with
      | nil =>
          simpa [PlannedCoercionPath.isValid, CoercionPath.isValid,
            head.source_eq, head.target_eq] using valid
      | @cons nextPlanned nextCommitted rest remaining nextHead nextTail =>
          simp only [PlannedCoercionPath.isValid, Bool.and_eq_true] at valid
          simp only [CoercionPath.isValid, Bool.and_eq_true]
          constructor
          · simpa [head.source_eq] using valid.1
          · have restValid := induction (by
              simpa [PlannedCoercionPath.isValid] using valid.2)
            simpa [head.target_eq, CoercionPath.isValid] using restValid

end CoercionPlanCommitCorresponds

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

/-- Unification does not remove rows from the canonical requirement ledger. -/
theorem unify_requirements_subset
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    state.requirements ⊆ next.requirements := by
  unfold unify at success
  cases unification : state.inference.unify left right with
  | error error =>
      simp [unification, liftUnification, bind, Except.bind] at success
  | ok inference =>
      simp only [unification, liftUnification, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      exact fun _ member => member

private theorem addRequirementWithId_requirements_subset
    (state : State) (predicate : ProgramPredicate) :
    state.requirements ⊆
      (state.addRequirementWithId predicate).2.requirements := by
  intro requirement member
  simp only [State.addRequirementWithId, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false]
  exact Or.inl member

private theorem addRequirementsWithIds_requirements_subset
    (state : State) (predicates : List ProgramPredicate) :
    state.requirements ⊆
      (state.addRequirementsWithIds predicates).2.requirements := by
  induction predicates generalizing state with
  | nil => exact fun _ member => member
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      exact List.Subset.trans
        (addRequirementWithId_requirements_subset state predicate)
        (induction (state.addRequirementWithId predicate).2)

private theorem addRequirementsWithIds_correspond
    (state : State) (predicates : List ProgramPredicate) :
    RequirementPredicatesCorrespond
      (state.addRequirementsWithIds predicates).2.requirements
      predicates (state.addRequirementsWithIds predicates).1 := by
  induction predicates generalizing state with
  | nil => exact .nil
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      apply RequirementPredicatesCorrespond.cons
      · exact addRequirementsWithIds_requirements_subset
          (state.addRequirementWithId predicate).2 rest
          (by simp [State.addRequirementWithId])
      · exact induction (state.addRequirementWithId predicate).2

private theorem addRequirementsWithIds_predicates
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.requirements.map
        (fun requirement => requirement.predicate) =
      state.requirements.map (fun requirement => requirement.predicate) ++
        predicates := by
  induction predicates generalizing state with
  | nil => simp [State.addRequirementsWithIds]
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      simp [State.addRequirementWithId, List.append_assoc]

private theorem commitCoercionPlan_requirements_subset
    (state : State) (plan : List PlannedCoercionStep) :
    state.requirements ⊆ (commitCoercionPlan state plan).2.requirements := by
  induction plan generalizing state with
  | nil => exact fun _ member => member
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      exact List.Subset.trans
        (addRequirementWithId_requirements_subset state step.predicate)
        (List.Subset.trans
          (addRequirementsWithIds_requirements_subset
            (state.addRequirementWithId step.predicate).2
            step.methodPredicates)
          (induction
            ((state.addRequirementWithId step.predicate).2
              |>.addRequirementsWithIds step.methodPredicates).2))

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

/-- Committing a selected coercion path preserves edge order and endpoints,
and every primary or method requirement identity stored on the committed path
points to the corresponding predicate row in the final ledger. -/
theorem commitCoercionPlan_corresponds
    (state : State) (plan : List PlannedCoercionStep) :
    CoercionPlanCommitCorresponds
      (commitCoercionPlan state plan).2.requirements
      plan (commitCoercionPlan state plan).1 := by
  induction plan generalizing state with
  | nil => exact .nil
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      apply CoercionPlanCommitCorresponds.cons
      · refine {
          source_eq := rfl
          target_eq := rfl
          primary_mem := ?_
          methods := ?_
        }
        · apply commitCoercionPlan_requirements_subset
            (((state.addRequirementWithId step.predicate).2
              |>.addRequirementsWithIds step.methodPredicates).2) rest
          apply addRequirementsWithIds_requirements_subset
            (state.addRequirementWithId step.predicate).2
            step.methodPredicates
          simp [State.addRequirementWithId]
        · apply RequirementPredicatesCorrespond.mono
            (commitCoercionPlan_requirements_subset
              (((state.addRequirementWithId step.predicate).2
                |>.addRequirementsWithIds step.methodPredicates).2) rest)
          exact addRequirementsWithIds_correspond
            (state.addRequirementWithId step.predicate).2
            step.methodPredicates
      · exact induction
          (((state.addRequirementWithId step.predicate).2
            |>.addRequirementsWithIds step.methodPredicates).2)

/-- Allocation changes only requirement identities: a structurally valid
planned path remains structurally valid after it is committed. -/
theorem commitCoercionPlan_isValid
    (state : State) {source target : Ty}
    (plan : List PlannedCoercionStep)
    (valid : PlannedCoercionPath.isValid source target plan = true) :
    CoercionPath.isValid source target (commitCoercionPlan state plan).1 =
      true := by
  exact (commitCoercionPlan_corresponds state plan).isValid valid

/-- No hidden obligations are introduced while committing a path: the final
ledger appends exactly each edge's primary predicate and then its method
predicates, preserving both edge order and method declaration order. -/
theorem commitCoercionPlan_requirementPredicates
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.requirements.map
        (fun requirement => requirement.predicate) =
      state.requirements.map (fun requirement => requirement.predicate) ++
        plan.flatMap PlannedCoercionStep.predicates := by
  induction plan generalizing state with
  | nil => simp [commitCoercionPlan]
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      rw [addRequirementsWithIds_predicates]
      simp [State.addRequirementWithId, PlannedCoercionStep.predicates,
        List.append_assoc]

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

/-- Successful expected-type fitting only retains or extends the input
requirement ledger.  In the mismatch branch the extension consists exactly of
the selected coercion path's primary and method obligations. -/
theorem withExpected_requirements_subset
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      exact fun _ member => member
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          exact fun _ member => member
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
                      exact commitCoercionPlan_requirements_subset state plan

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

/-- A retained expected-type candidate only retains or extends the input
requirement ledger. -/
theorem candidateWithExpected_requirements_subset
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    state.requirements ⊆ result.state.requirements := by
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
      exact withExpected_requirements_subset fittedResult

/-- Fitting an argument spine preserves the canonical requirement ledger.
Every requirement added by an inserted coercion is committed by the
corresponding successful `candidateWithExpected` step. -/
theorem fitArguments_preserves_requirementsWellFormed
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result))
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      exact wellFormed
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none =>
                  simp only [fittedResult, bind, Except.bind] at success
                  change Except.ok (none : Option ArgumentFitResult) =
                    Except.ok (some result) at success
                  simp at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  have fittedWellFormed :
                      fitted.state.RequirementsWellFormed :=
                    candidateWithExpected_preserves_requirementsWellFormed
                      fittedResult wellFormed
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult] at success
                  | ok tail? =>
                      cases tail? with
                      | none =>
                          simp only [tailResult] at success
                          change Except.ok (none : Option ArgumentFitResult) =
                            Except.ok (some result) at success
                          simp at success
                      | some tail =>
                          simp only [tailResult] at success
                          change Except.ok (some {
                            state := tail.state
                            cost := fitted.coercions.length + tail.cost
                            coercions := {
                              expression := argument.id
                              coercions := fitted.coercions
                            } :: tail.coercions
                          }) = Except.ok (some result) at success
                          injection success with resultEq
                          have resultEq : _ = result :=
                            Option.some.inj resultEq
                          subst result
                          exact induction (result := tail) tailResult
                            fittedWellFormed

/-- Fitting an argument spine only retains or extends the input requirement
ledger.  Each recursive step starts from the state produced by the preceding
expected-type fit. -/
theorem fitArguments_requirements_subset
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    state.requirements ⊆ result.state.requirements := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      exact fun _ member => member
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none =>
                  simp only [fittedResult, bind, Except.bind] at success
                  change Except.ok (none : Option ArgumentFitResult) =
                    Except.ok (some result) at success
                  simp at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  have fittedSubset :
                      state.requirements ⊆ fitted.state.requirements :=
                    candidateWithExpected_requirements_subset fittedResult
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult] at success
                  | ok tail? =>
                      cases tail? with
                      | none =>
                          simp only [tailResult] at success
                          change Except.ok (none : Option ArgumentFitResult) =
                            Except.ok (some result) at success
                          simp at success
                      | some tail =>
                          simp only [tailResult] at success
                          change Except.ok (some {
                            state := tail.state
                            cost := fitted.coercions.length + tail.cost
                            coercions := {
                              expression := argument.id
                              coercions := fitted.coercions
                            } :: tail.coercions
                          }) = Except.ok (some result) at success
                          injection success with resultEq
                          have resultEq : _ = result :=
                            Option.some.inj resultEq
                          subst result
                          exact List.Subset.trans fittedSubset
                            (induction (result := tail) tailResult)

/-- A retained function candidate preserves the canonical requirement ledger.
The integer-literal and predicate validators return only `Bool`/`Unit`; they
inspect the fitted state but do not construct a replacement state.  The only
later state changes append the instantiated signature requirements and record
their direct-call provenance. -/
theorem tryFunctionCandidate_preserves_requirementsWellFormed
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result))
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try
    have fittedArgumentsWellFormed :=
      fitArguments_preserves_requirementsWellFormed (by assumption) (by
        change state.RequirementsWellFormed
        exact wellFormed)
  all_goals try
    have fittedResultWellFormed :=
      candidateWithExpected_preserves_requirementsWellFormed (by assumption)
        fittedArgumentsWellFormed
  all_goals
    exact State.markDirectCallRequirements_preserves_requirementsWellFormed _ _
      (State.addRequirementsWithIds_preserves_requirementsWellFormed _ _
        fittedResultWellFormed)

/-- A retained function candidate only retains or extends the input
requirement ledger.  Argument/result coercions and instantiated signature
predicates are appended in execution order. -/
theorem tryFunctionCandidate_requirements_subset
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    state.requirements ⊆ result.state.requirements := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try
    have fittedArgumentsSubset :=
      fitArguments_requirements_subset (by assumption)
  all_goals try
    have fittedResultSubset :=
      candidateWithExpected_requirements_subset (by assumption)
  all_goals
    exact List.Subset.trans
      (by
        change state.requirements ⊆ state.requirements
        exact fun _ member => member)
      (List.Subset.trans fittedArgumentsSubset
        (List.Subset.trans fittedResultSubset
          (addRequirementsWithIds_requirements_subset _ _)))

private theorem collectCandidateAttempts_success_requirements_subset
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {state : State}
    (attemptSubset : ∀ signature result,
      attempt signature = .ok (some result) →
        state.requirements ⊆ result.state.requirements) :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        state.requirements ⊆ success.attempt.state.requirements := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro selected member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction selected member
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction selected member
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl selectedEq =>
                  subst selected
                  exact attemptSubset signature result attemptResult
              | inr member => exact induction selected member

private theorem bestCandidateSuccesses_requirements_subset
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

/-- Explicit-candidate overload selection returns a successful candidate whose
ledger only retains or extends the shared input ledger. -/
theorem selectFunctionCandidateFrom_requirements_subset
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
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
              bestCandidateSuccesses_requirements_subset search.successes
                (by simp [selected])
            exact collectCandidateAttempts_success_requirements_subset
              (state := state)
              (fun signature attemptResult attemptSuccess =>
                tryFunctionCandidate_requirements_subset attemptSuccess)
              candidates candidate member

/-- Resolving the visible overload set does not alter the input state, so
ordinary overload selection inherits explicit-candidate ledger monotonicity. -/
theorem selectFunctionCandidate_requirements_subset
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_requirements_subset success

private theorem pureState_eq
    {state next : State}
    (success : (pure state : Except Error State) = .ok next) :
    state = next := by
  change Except.ok state = Except.ok next at success
  exact Except.ok.inj success

private theorem exceptPure_eq {epsilon alpha : Type} {value result : alpha}
    (success : (pure value : Except epsilon alpha) = .ok result) :
    value = result := by
  change Except.ok value = Except.ok result at success
  exact Except.ok.inj success

private theorem exceptPure_eq_ok {epsilon alpha : Type}
    (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

/-- Unary-operator inference changes only unification metadata and may append
the selected trait method's obligations. -/
theorem inferUnaryOperator_requirements_subset
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals intro requirement member
  all_goals solve_by_elim [unify_requirements_subset,
    addRequirementsWithIds_requirements_subset]

/-- Binary-operator inference changes only unification metadata and may append
the selected trait method's obligations. -/
theorem inferBinaryOperator_requirements_subset
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals intro requirement member
  all_goals try solve_by_elim [unify_requirements_subset,
    addRequirementsWithIds_requirements_subset]
  all_goals
    apply addRequirementsWithIds_requirements_subset _ _
    solve_by_elim [unify_requirements_subset]

/-- Attaching already allocated coercion metadata changes expression nodes but
does not change the canonical requirement ledger. -/
theorem attachExpressionCoercions_preserves_requirementsWellFormed
    (state : State) (entries : List ExpressionCoercions)
    (wellFormed : state.RequirementsWellFormed) :
    (attachExpressionCoercions state entries).RequirementsWellFormed := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil =>
      exact wellFormed
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact induction _
        (State.modifyExpressionNode_preserves_requirementsWellFormed
          state entry.expression _ wellFormed)

/-- Attaching already allocated coercion metadata does not remove requirement
ledger rows. -/
theorem attachExpressionCoercions_requirements_subset
    (state : State) (entries : List ExpressionCoercions) :
    state.requirements ⊆
      (attachExpressionCoercions state entries).requirements := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact fun _ member => member
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact induction
        (state.modifyExpressionNode entry.expression fun node => {
          node with
          type := entry.coercions.foldl (fun _ step => step.target) node.type
          requirements :=
            node.requirements ++ coercionRequirements entry.coercions
          coercions := node.coercions ++ entry.coercions
        })

/-- Recording one expression node preserves the canonical requirement
ledger.  Requirement identities stored on the node are references to the
existing ledger, not new allocations. -/
theorem recordExpression_preserves_requirementsWellFormed
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (wellFormed : state.RequirementsWellFormed) :
    State.RequirementsWellFormed
      (recordExpression source expression form requirements coercions state).2 := by
  exact State.recordNode_preserves_requirementsWellFormed state _ wellFormed

/-- Recording one expression node does not remove requirement ledger rows. -/
theorem recordExpression_requirements_subset
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State) :
    state.requirements ⊆
      (recordExpression source expression form requirements coercions
        state).2.requirements := by
  exact fun _ member => member

/-- Expected-type fitting may allocate coercion requirements; recording the
resulting node itself leaves that fitted ledger unchanged. -/
theorem recordExpressionWithExpected_preserves_requirementsWellFormed
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.2.RequirementsWellFormed := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error =>
      simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok (recordExpression source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact recordExpression_preserves_requirementsWellFormed
        source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state
        (withExpected_preserves_requirementsWellFormed fittedResult wellFormed)

/-- Expected-type fitting may append coercion obligations; recording the
resulting expression node does not remove any input ledger row. -/
theorem recordExpressionWithExpected_requirements_subset
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error =>
      simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok (recordExpression source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact List.Subset.trans (withExpected_requirements_subset fittedResult)
        (recordExpression_requirements_subset source fitted.expression form
          (requirements ++ coercionRequirements fitted.coercions)
          fitted.coercions fitted.state)

/-- Recording the callee and call nodes for a selected declaration preserves
the explicitly supplied state ledger. -/
theorem recordSelectedCallResult_preserves_requirementsWellFormed
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) (wellFormed : state.RequirementsWellFormed) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.RequirementsWellFormed := by
  let attachedState :=
    attachExpressionCoercions state attempt.argumentCoercions
  have attachedWellFormed : attachedState.RequirementsWellFormed :=
    attachExpressionCoercions_preserves_requirementsWellFormed
      state attempt.argumentCoercions wellFormed
  let allocation := attachedState.allocateExpressionId
  have allocatedWellFormed : allocation.2.RequirementsWellFormed :=
    State.allocateExpressionId_preserves_requirementsWellFormed
      attachedState attachedWellFormed
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  have calleeWellFormed : calleeRecord.2.RequirementsWellFormed :=
    recordExpression_preserves_requirementsWellFormed callee calleeExpression
      (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
      allocatedWellFormed
  change State.RequirementsWellFormed
    (recordExpression source result
      (.call allocation.1 (arguments.map (fun argument => argument.id))
        (.declaration attempt.instantiation))
      (coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        coercionRequirements trailingCoercions)
      (attempt.callCoercions ++ trailingCoercions) calleeRecord.2).2
  exact recordExpression_preserves_requirementsWellFormed source result _ _ _ _
    calleeWellFormed

/-- Recording selected-call provenance and expression nodes does not remove
rows from the explicitly supplied requirement ledger. -/
theorem recordSelectedCallResult_requirements_subset
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    state.requirements ⊆
      (recordSelectedCallResult source callee name arguments attempt result
        trailingCoercions state).2.requirements := by
  let attachedState :=
    attachExpressionCoercions state attempt.argumentCoercions
  have attachedSubset :
      state.requirements ⊆ attachedState.requirements :=
    attachExpressionCoercions_requirements_subset
      state attempt.argumentCoercions
  let allocation := attachedState.allocateExpressionId
  have allocatedSubset :
      attachedState.requirements ⊆ allocation.2.requirements :=
    fun _ member => member
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  let calleeRecord := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  have calleeSubset :
      allocation.2.requirements ⊆ calleeRecord.2.requirements :=
    recordExpression_requirements_subset callee calleeExpression
      (.reference name (.declaration attempt.instantiation)) [] [] allocation.2
  change state.requirements ⊆
    (recordExpression source result
      (.call allocation.1 (arguments.map (fun argument => argument.id))
        (.declaration attempt.instantiation))
      (coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        coercionRequirements trailingCoercions)
      (attempt.callCoercions ++ trailingCoercions) calleeRecord.2).2.requirements
  exact List.Subset.trans attachedSubset
    (List.Subset.trans allocatedSubset
      (List.Subset.trans calleeSubset
        (recordExpression_requirements_subset source result _ _ _
          calleeRecord.2)))

/-- Recording an ordinary selected call preserves the selected attempt's
canonical requirement ledger. -/
theorem recordSelectedCall_preserves_requirementsWellFormed
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (wellFormed : attempt.state.RequirementsWellFormed) :
    State.RequirementsWellFormed
      (recordSelectedCall source callee name arguments attempt).2 := by
  exact recordSelectedCallResult_preserves_requirementsWellFormed
    source callee name arguments attempt attempt.result [] attempt.state
    wellFormed

/-- Recording an ordinary selected call does not remove rows from the
selected attempt's requirement ledger. -/
theorem recordSelectedCall_requirements_subset
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    attempt.state.requirements ⊆
      (recordSelectedCall source callee name arguments attempt).2.requirements := by
  exact recordSelectedCallResult_requirements_subset
    source callee name arguments attempt attempt.result [] attempt.state

/-- Recording an indirect call adds one node and preserves the application
result state's canonical requirement ledger. -/
theorem recordIndirectCall_preserves_requirementsWellFormed
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult)
    (wellFormed : result.state.RequirementsWellFormed) :
    State.RequirementsWellFormed
      (recordIndirectCall source callee arguments result).2 := by
  unfold recordIndirectCall
  exact recordExpression_preserves_requirementsWellFormed _ _ _ _ _ _
    wellFormed

/-- Recording an indirect call does not remove rows from the application
result's requirement ledger. -/
theorem recordIndirectCall_requirements_subset
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    result.state.requirements ⊆
      (recordIndirectCall source callee arguments result).2.requirements := by
  unfold recordIndirectCall
  exact recordExpression_requirements_subset _ _ _ _ _ _

/-- Applying an indirectly obtained function type may append coercion
requirements while retaining every row from the input ledger. -/
theorem applyFunctionType_requirements_subset
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
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
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact List.Subset.trans
                (withExpected_requirements_subset argumentResult)
                (withExpected_requirements_subset resultResult)
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
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have freshSubset :
                  state.requirements ⊆ freshState.requirements := by
                have subset := State.fresh_requirements_subset state
                rw [freshResultEq] at subset
                exact subset
              exact List.Subset.trans freshSubset
                (List.Subset.trans (unify_requirements_subset unifyResult)
                  (withExpected_requirements_subset resultResult))

/-- Binding lambda parameters changes only inference and lexical metadata, so
it retains the input requirement ledger. -/
theorem bindLambdaParameters_requirements_subset
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    state.requirements ⊆ result.2.2.requirements := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact fun _ member => member
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailSubset := induction _ _ _ (by assumption)
            simpa [State.fresh, State.allocateBinder] using tailSubset
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all only [exceptPure_eq_ok]
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailSubset := induction _ _ _ (by assumption)
                simpa [State.allocateBinder] using tailSubset

/-- Allocating a list of fresh types does not remove requirement rows. -/
theorem freshTypes_requirements_subset (count : Nat) (state : State) :
    state.requirements ⊆ (freshTypes count state).2.requirements := by
  induction count generalizing state with
  | zero => exact fun _ member => member
  | succ count induction =>
      simpa [freshTypes, State.fresh] using induction state.fresh.2

/-- Freshening a data-constructor instantiation changes no requirement rows. -/
theorem freshDataConstructorInstantiation_requirements_subset
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    state.requirements ⊆
      (freshDataConstructorInstantiation dataType constructor
        state).2.requirements := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldSubset (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      accumulator.2.requirements ⊆
        (parameters.foldl step accumulator).2.requirements := by
    induction parameters generalizing accumulator with
    | nil => exact fun _ member => member
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        simpa [step, State.fresh] using
          induction (step accumulator parameter)
  unfold freshDataConstructorInstantiation
  exact foldSubset dataType.parameters ([], state)

private def PreservesRequirements {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result →
    initial.requirements ⊆ (stateOf result).requirements

private theorem inferMatchPatternFlatFuel_preserves_requirements
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesRequirements InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        PreservesRequirements InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        PreservesRequirements InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesRequirements at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try have unifySubset :=
      unify_requirements_subset (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.allocateBinder]
    all_goals intro requirement member
    all_goals try grind
      [unify_requirements_subset,
        State.addRequirementWithId_requirements_subset,
        State.allocateBinder_requirements_subset,
        freshDataConstructorInstantiation_requirements_subset,
        freshTypes_requirements_subset]

/-- Successful pattern inference only retains or extends the input requirement
ledger. -/
theorem inferMatchPatternFuel_requirements_subset
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    state.requirements ⊆ result.2.requirements := by
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
      exact inferMatchPatternFlatFuel_preserves_requirements fuel context pattern
        expected [] state inferred flatResult

/-- Pairwise builtin argument unification does not remove requirement rows. -/
theorem unifyBuiltinFunctionArgumentsEqual_requirements_subset
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    state.requirements ⊆ next.requirements := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      exact fun _ member => member
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          exact fun _ member => member
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unified =>
              simp only [unifyResult, bind, Except.bind] at success
              exact List.Subset.trans
                (unify_requirements_subset unifyResult)
                (induction success)

/-- Recording a fixed builtin call changes inference metadata and source nodes
without removing input requirement rows. -/
theorem recordBuiltinFunctionCall_requirements_subset
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals intro requirement member
  all_goals solve_by_elim (maxDepth := 12)
    [unifyBuiltinFunctionArgumentsEqual_requirements_subset,
      unify_requirements_subset,
      State.allocateExpressionId_requirements_subset,
      recordExpression_requirements_subset]

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
