import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.StateProperties

/-! Small preservation laws for function-local source obligation identities. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

private theorem nodup_of_mapped_nodup
    {alpha beta : Type} (values : List alpha) (key : alpha → beta)
    (mappedNodup : (values.map key).Nodup) : values.Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup ⊢
      refine ⟨?_, induction mappedNodup.2⟩
      intro member
      exact mappedNodup.1 (List.mem_map.mpr ⟨_, member, rfl⟩)

private theorem eq_of_mem_of_mapped_nodup
    {alpha beta : Type} {values : List alpha} (key : alpha → beta)
    (mappedNodup : (values.map key).Nodup)
    {left right : alpha} (leftMem : left ∈ values)
    (rightMem : right ∈ values) (keyEq : key left = key right) :
    left = right := by
  induction values generalizing left right with
  | nil => simp at leftMem
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨right, rightMem, keyEq.symm⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨left, leftMem, keyEq⟩
        · exact induction tailNodup leftMem rightMem keyEq

private theorem requirementIds_nodup_of_indices_nodup
    (ids : List RequirementId)
    (indices : (ids.map (fun id => id.index)).Nodup) : ids.Nodup := by
  exact nodup_of_mapped_nodup ids (fun id => id.index) indices

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

/-- Canonical allocation keeps the ledger length synchronized with the next
fresh requirement identity. -/
theorem requirements_length_eq_nextRequirement (state : State)
    (wellFormed : state.RequirementsWellFormed) :
    state.requirements.length = state.nextRequirement := by
  change state.requirements.map (fun requirement => requirement.id.index) =
    List.range state.nextRequirement at wellFormed
  have lengths := congrArg List.length wellFormed
  simpa using lengths

/-- Every retained row was allocated strictly before the state's next fresh
requirement identity. -/
theorem requirement_id_lt_nextRequirement (state : State)
    (wellFormed : state.RequirementsWellFormed)
    {requirement : Requirement} (member : requirement ∈ state.requirements) :
    requirement.id.index < state.nextRequirement := by
  change state.requirements.map (fun candidate => candidate.id.index) =
    List.range state.nextRequirement at wellFormed
  have indexMember : requirement.id.index ∈
      state.requirements.map (fun candidate => candidate.id.index) :=
    List.mem_map.mpr ⟨requirement, member, rfl⟩
  rw [wellFormed] at indexMember
  exact List.mem_range.mp indexMember

/-- Batch allocation returns the consecutive identity interval beginning at
the input state's fresh-requirement boundary, in predicate order. -/
theorem addRequirementsWithIds_id_indices
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).1.map (fun id => id.index) =
      List.range' state.nextRequirement predicates.length := by
  induction predicates generalizing state with
  | nil => simp [addRequirementsWithIds]
  | cons predicate rest induction =>
      simp [addRequirementsWithIds, addRequirementWithId,
        List.range'_succ, induction]

/-- Identities returned by one batch allocation are pairwise distinct even
when the requested predicates themselves contain duplicates. -/
theorem addRequirementsWithIds_ids_nodup
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).1.Nodup := by
  apply requirementIds_nodup_of_indices_nodup
  rw [addRequirementsWithIds_id_indices]
  exact List.nodup_range'

/-- In a canonical state, every identity returned by batch allocation is
fresh for the complete input ledger. -/
theorem addRequirementsWithIds_ids_fresh
    (state : State) (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed) :
    ∀ id, id ∈ (state.addRequirementsWithIds predicates).1 →
      id ∉ state.requirements.map (fun requirement => requirement.id) := by
  intro id allocated existing
  have allocatedIndex : id.index ∈
      List.range' state.nextRequirement predicates.length := by
    rw [← addRequirementsWithIds_id_indices state predicates]
    exact List.mem_map.mpr ⟨id, allocated, rfl⟩
  have atLeast : state.nextRequirement ≤ id.index :=
    (List.mem_range'_1.mp allocatedIndex).1
  rcases List.mem_map.mp existing with
    ⟨requirement, requirementMember, requirementIdEq⟩
  have below := requirement_id_lt_nextRequirement state wellFormed
    requirementMember
  rw [requirementIdEq] at below
  exact (Nat.not_lt_of_ge atLeast) below

/-- In a canonical ledger, taking the first `cutoff` rows selects exactly the
rows whose stable identity lies below that cutoff. -/
theorem mem_take_requirements_iff (state : State)
    (wellFormed : state.RequirementsWellFormed) (cutoff : Nat)
    (requirement : Requirement) :
    requirement ∈ state.requirements.take cutoff ↔
      requirement ∈ state.requirements ∧ requirement.id.index < cutoff := by
  change state.requirements.map (fun candidate => candidate.id.index) =
    List.range state.nextRequirement at wellFormed
  constructor
  · intro member
    have indexMember : requirement.id.index ∈
        (state.requirements.take cutoff).map
          (fun candidate => candidate.id.index) :=
      List.mem_map.mpr ⟨requirement, member, rfl⟩
    rw [List.map_take, wellFormed, List.take_range] at indexMember
    have belowMinimum := List.mem_range.mp indexMember
    exact ⟨List.mem_of_mem_take member,
      Nat.lt_of_lt_of_le belowMinimum (Nat.min_le_left _ _)⟩
  · rintro ⟨member, belowCutoff⟩
    have belowNext : requirement.id.index < state.nextRequirement := by
      have indexMember : requirement.id.index ∈
          state.requirements.map (fun candidate => candidate.id.index) :=
        List.mem_map.mpr ⟨requirement, member, rfl⟩
      rw [wellFormed] at indexMember
      exact List.mem_range.mp indexMember
    have indexMember : requirement.id.index ∈
        (state.requirements.take cutoff).map
          (fun candidate => candidate.id.index) := by
      rw [List.map_take, wellFormed, List.take_range, List.mem_range]
      exact Nat.lt_min.mpr ⟨belowCutoff, belowNext⟩
    rcases List.mem_map.mp indexMember with
      ⟨candidate, candidateMember, indexEq⟩
    have indicesNodup :
        (state.requirements.map
          (fun candidate => candidate.id.index)).Nodup := by
      rw [wellFormed]
      exact List.nodup_range
    have candidateEq : candidate = requirement :=
      eq_of_mem_of_mapped_nodup
        (fun candidate : Requirement => candidate.id.index) indicesNodup
        (List.mem_of_mem_take candidateMember) member indexEq
    simpa [candidateEq] using candidateMember

/-- A canonical ledger extension retains exactly the prior rows below the
prior state's fresh-identity boundary, including each row's predicate
payload. -/
theorem mem_take_prior_requirements_iff
    (before after : State)
    (beforeWellFormed : before.RequirementsWellFormed)
    (afterWellFormed : after.RequirementsWellFormed)
    (included : before.requirements ⊆ after.requirements)
    (requirement : Requirement) :
    requirement ∈ after.requirements.take before.nextRequirement ↔
      requirement ∈ before.requirements := by
  constructor
  · intro taken
    have takenCharacterization :=
      (mem_take_requirements_iff after afterWellFormed
        before.nextRequirement requirement).mp taken
    rcases takenCharacterization with ⟨afterMember, belowBefore⟩
    have beforeIndices :
        before.requirements.map
            (fun candidate => candidate.id.index) =
          List.range before.nextRequirement := by
      exact beforeWellFormed
    have beforeIndexMember : requirement.id.index ∈
        before.requirements.map
          (fun candidate => candidate.id.index) := by
      rw [beforeIndices, List.mem_range]
      exact belowBefore
    rcases List.mem_map.mp beforeIndexMember with
      ⟨candidate, candidateBefore, indexEq⟩
    have afterIndices :
        after.requirements.map
            (fun candidate => candidate.id.index) =
          List.range after.nextRequirement := by
      exact afterWellFormed
    have afterIndicesNodup :
        (after.requirements.map
          (fun candidate => candidate.id.index)).Nodup := by
      rw [afterIndices]
      exact List.nodup_range
    have candidateEq : candidate = requirement :=
      eq_of_mem_of_mapped_nodup
        (fun candidate : Requirement => candidate.id.index)
        afterIndicesNodup (included candidateBefore) afterMember indexEq
    simpa [candidateEq] using candidateBefore
  · intro beforeMember
    exact (mem_take_requirements_iff after afterWellFormed
      before.nextRequirement requirement).mpr
        ⟨included beforeMember,
          requirement_id_lt_nextRequirement before beforeWellFormed
            beforeMember⟩

/-- Dually, dropping the first `cutoff` rows selects exactly the rows whose
stable identity is at least that cutoff. -/
theorem mem_drop_requirements_iff (state : State)
    (wellFormed : state.RequirementsWellFormed) (cutoff : Nat)
    (requirement : Requirement) :
    requirement ∈ state.requirements.drop cutoff ↔
      requirement ∈ state.requirements ∧ cutoff ≤ requirement.id.index := by
  have rowsNodup : state.requirements.Nodup :=
    nodup_of_mapped_nodup state.requirements
      (fun candidate : Requirement => candidate.id)
      (requirementIds_nodup state wellFormed)
  constructor
  · intro dropped
    have member := (List.drop_sublist cutoff state.requirements).subset dropped
    refine ⟨member, ?_⟩
    apply Nat.le_of_not_gt
    intro belowCutoff
    have taken : requirement ∈ state.requirements.take cutoff :=
      (mem_take_requirements_iff state wellFormed cutoff requirement).mpr
        ⟨member, belowCutoff⟩
    have splitNodup :
        (state.requirements.take cutoff ++
          state.requirements.drop cutoff).Nodup := by
      rw [List.take_append_drop]
      exact rowsNodup
    have separated := (List.nodup_append.mp splitNodup).2.2
    exact (separated requirement taken requirement dropped) rfl
  · rintro ⟨member, atLeast⟩
    have splitMember : requirement ∈
        state.requirements.take cutoff ++
          state.requirements.drop cutoff := by
      rw [List.take_append_drop]
      exact member
    rcases List.mem_append.mp splitMember with taken | dropped
    · have belowCutoff :=
        ((mem_take_requirements_iff state wellFormed cutoff requirement).mp
          taken).2
      exact False.elim ((Nat.not_lt_of_ge atLeast) belowCutoff)
    · exact dropped

/-- Every retained integer-literal node decodes to its recorded value, owns
matching origin metadata, and names the exact builtin-`Int` row retained in
the canonical requirement ledger. -/
def IntegerLiteralLedgerCorrespondence (state : State) : Prop :=
  ∀ node source resolution,
    Node.expression node ∈ state.nodes →
    node.form = .integerLiteral source resolution →
    Frontend.numericLiteralValue? source = some resolution.rawValue ∧
      ∃ origin, origin ∈ state.integerLiterals ∧
        origin.expression = node.id ∧
        resolution.targetType = .variable origin.metavariable ∧
        resolution.requirement = origin.requirement ∧
        ({ id := resolution.requirement, predicate := resolution.predicate } :
          Requirement) ∈ state.requirements

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

namespace State

/-- Batch allocation retains the exact predicate/identity pairing returned to
the caller.  In particular, the correspondence is stated against the final
ledger, so later source-semantics proofs can consume it without replaying the
recursive allocator. -/
theorem addRequirementsWithIds_correspond
    (state : State) (predicates : List ProgramPredicate) :
    RequirementPredicatesCorrespond
      (state.addRequirementsWithIds predicates).2.requirements
      predicates (state.addRequirementsWithIds predicates).1 := by
  induction predicates generalizing state with
  | nil => exact .nil
  | cons predicate rest induction =>
      simp only [addRequirementsWithIds]
      apply RequirementPredicatesCorrespond.cons
      · exact addRequirementsWithIds_requirements_subset
          (state.addRequirementWithId predicate).2 rest
          (by simp [addRequirementWithId])
      · exact induction (state.addRequirementWithId predicate).2

/-- The allocation facts needed by a generalized-local reference: its actual
obligation IDs follow the instantiated predicate spine, are pairwise fresh,
and cannot reuse any template ID owned by the selected binder. -/
structure LookupBinderRequirementAllocationCertificate
    (state : State) (binder : TypedBinder)
    (predicates : List ProgramPredicate) : Prop where
  correspondence : RequirementPredicatesCorrespond
    (state.addRequirementsWithIds predicates).2.requirements
    predicates (state.addRequirementsWithIds predicates).1
  ids_nodup : (state.addRequirementsWithIds predicates).1.Nodup
  actual_ids_fresh_for_templates :
    ∀ id, id ∈ (state.addRequirementsWithIds predicates).1 →
      id ∉ binder.schemeRequirements.map
        (fun requirement => requirement.templateRequirement)

/-- Successful guarded lookup and canonical ledger tracking turn one batch
allocation into the complete identity certificate required at a generalized
local use site. -/
theorem addRequirementsWithIds_lookupBinder_certificate
    (state : State) (name : String) (binder : TypedBinder)
    (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed)
    (assumptionsContained : state.localSchemeAssumptions ⊆
      state.requirements.map (fun requirement => requirement.id))
    (found : state.lookupBinder? name = some binder) :
    LookupBinderRequirementAllocationCertificate state binder predicates := by
  refine ⟨addRequirementsWithIds_correspond state predicates,
    addRequirementsWithIds_ids_nodup state predicates, ?_⟩
  intro id allocated template
  exact addRequirementsWithIds_ids_fresh state predicates wellFormed id
    allocated
    (assumptionsContained
      (lookupBinder?_eq_some_templates_subset found template))

end State

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
          exact State.addRequirementsWithIds_correspond
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
    {localSchemeInstantiationStart : Option Nat}
    (wellFormed : state.RequirementsWellFormed) :
    State.RequirementsWellFormed
      (recordExpression source expression form requirements coercions state
        localSchemeInstantiationStart).2 := by
  exact State.recordNode_preserves_requirementsWellFormed state _ wellFormed

/-- Recording one expression node does not remove requirement ledger rows. -/
theorem recordExpression_requirements_subset
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    state.requirements ⊆
      (recordExpression source expression form requirements coercions
        state localSchemeInstantiationStart).2.requirements := by
  exact fun _ member => member

/-- Expected-type fitting may allocate coercion requirements; recording the
resulting node itself leaves that fitted ledger unchanged. -/
theorem recordExpressionWithExpected_preserves_requirementsWellFormed
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result)
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
        fitted.coercions fitted.state localSchemeInstantiationStart) =
          Except.ok result at success
      injection success with resultEq
      subst result
      exact recordExpression_preserves_requirementsWellFormed
        source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state
        (localSchemeInstantiationStart := localSchemeInstantiationStart)
        (withExpected_preserves_requirementsWellFormed fittedResult wellFormed)

/-- Expected-type fitting may append coercion obligations; recording the
resulting expression node does not remove any input ledger row. -/
theorem recordExpressionWithExpected_requirements_subset
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error =>
      simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok (recordExpression source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state localSchemeInstantiationStart) =
          Except.ok result at success
      injection success with resultEq
      subst result
      exact List.Subset.trans (withExpected_requirements_subset fittedResult)
        (recordExpression_requirements_subset source fitted.expression form
          (requirements ++ coercionRequirements fitted.coercions)
          fitted.coercions fitted.state
          (localSchemeInstantiationStart := localSchemeInstantiationStart))

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

/-- Unification changes only the inference substitution, so the numeric-pattern
origin list and canonical requirement ledger remain byte-for-byte identical.
This packages the two equalities needed to transport the exact origin-to-row
correspondence established by the integer-pattern inference branch. -/
theorem unify_integerPatternMetadata_eq
    {before after : State} {left right : Ty}
    (success : unify before left right = .ok after) :
    after.integerPatterns = before.integerPatterns ∧
      after.requirements = before.requirements := by
  unfold unify at success
  cases unified : before.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at success
  cases success
  exact ⟨rfl, rfl⟩

private theorem freshTypes_integerPatterns_eq (count : Nat) (state : State) :
    (freshTypes count state).2.integerPatterns = state.integerPatterns := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [freshTypes]
      exact (induction state.fresh.2).trans rfl

private theorem freshDataConstructorInstantiation_integerPatterns_eq
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor
      state).2.integerPatterns = state.integerPatterns := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldEq (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.integerPatterns =
        accumulator.2.integerPatterns := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        exact (induction (step accumulator parameter)).trans rfl
  unfold freshDataConstructorInstantiation
  exact foldEq dataType.parameters ([], state)

private def PreservesIntegerPatterns {alpha : Type}
    (stateOf : alpha → State) (initial : State)
    (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result →
    initial.integerPatterns ⊆ (stateOf result).integerPatterns

private theorem unify_integerPatterns_subset
    {before after : State} {left right : Ty}
    (success : unify before left right = .ok after) :
    before.integerPatterns ⊆ after.integerPatterns := by
  rw [(unify_integerPatternMetadata_eq success).1]
  exact fun _ member => member

private theorem inferMatchPatternFlatFuel_preserves_integerPatterns
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesIntegerPatterns InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        PreservesIntegerPatterns InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        PreservesIntegerPatterns InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesIntegerPatterns at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try have unifySubset :=
      unify_integerPatterns_subset (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.addRequirementWithId,
      State.allocateBinder]
    all_goals intro origin member
    all_goals try grind
      [freshDataConstructorInstantiation_integerPatterns_eq,
        freshTypes_integerPatterns_eq]

/-- Successful flat pattern inference never removes an integer-pattern
origin retained by its input state. -/
theorem inferMatchPatternFlatFuel_integerPatterns_subset
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {seen : List String} {state : State}
    {result : InferredPattern}
    (success : inferMatchPatternFlatFuel fuel context pattern expected seen state =
      .ok result) :
    state.integerPatterns ⊆ result.state.integerPatterns := by
  exact inferMatchPatternFlatFuel_preserves_integerPatterns fuel context pattern
    expected seen state result success

/-- Successful source-ordered flat pattern-list inference likewise retains
every integer-pattern origin present at entry. -/
theorem inferMatchPatternsFlatFuel_integerPatterns_subset
    {fuel : Nat} {context : Context} {patterns : List Syntax.Pattern}
    {expected : List Ty} {seen : List String} {state : State}
    {result : InferredPatterns}
    (success : inferMatchPatternsFlatFuel fuel context patterns expected seen
      state = .ok result) :
    state.integerPatterns ⊆ result.state.integerPatterns := by
  induction patterns generalizing expected seen state result with
  | nil =>
      cases expected with
      | nil =>
          simp only [inferMatchPatternsFlatFuel, pure, Pure.pure, Except.pure]
            at success
          injection success with resultEq
          subst result
          exact fun _ member => member
      | cons type types =>
          simp [inferMatchPatternsFlatFuel] at success
  | cons pattern patterns induction =>
      cases expected with
      | nil => simp [inferMatchPatternsFlatFuel] at success
      | cons type types =>
          simp only [inferMatchPatternsFlatFuel, bind, Except.bind] at success
          cases headSuccess : inferMatchPatternFlatFuel fuel context pattern type
              seen state with
          | error error => simp [headSuccess] at success
          | ok head =>
              simp only [headSuccess] at success
              cases tailSuccess : inferMatchPatternsFlatFuel fuel context patterns
                  types head.names head.state with
              | error error => simp [tailSuccess] at success
              | ok tail =>
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  subst result
                  have tailSubset :
                      head.state.integerPatterns ⊆ tail.state.integerPatterns :=
                    induction tailSuccess
                  exact List.Subset.trans
                    (inferMatchPatternFlatFuel_integerPatterns_subset
                      headSuccess)
                    tailSubset

/-- The public pattern-inference wrapper retains every integer-pattern origin
present in its input state. -/
theorem inferMatchPatternFuel_integerPatterns_subset
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    state.integerPatterns ⊆ result.2.integerPatterns := by
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
      exact inferMatchPatternFlatFuel_integerPatterns_subset flatResult

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

/-- A successful direct numeric-pattern branch retains one exact metadata
origin and its matching builtin-`Int` requirement row.  In particular, this
does not merely recover a requirement identity from the pattern resolution:
it reconnects that identity to both ledgers which finalization later uses. -/
theorem inferMatchPatternFlatFuel_integerLiteral_metadata
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {literal : Syntax.CoreLiteral} {value : Syntax.CoreLiteralValue}
    {expected : Ty} {seen : List String} {state : State}
    {result : InferredPattern} {rawValue : Nat}
    (patternValue : pattern.value = .literal literal)
    (literalValue : literal.value = value)
    (numeric : Frontend.numericLiteralValue? value = some rawValue)
    (success : inferMatchPatternFlatFuel fuel context pattern expected seen state =
      .ok result) :
    ∃ resolution origin,
      result.resolution = .integerLiteral value resolution ∧
      result.requirements = [resolution.requirement] ∧
      resolution.rawValue = rawValue ∧
      resolution.targetType = .variable origin.metavariable ∧
      resolution.requirement = origin.requirement ∧
      origin.span = pattern.span ∧
      origin ∈ result.state.integerPatterns ∧
      ({ id := origin.requirement,
          predicate := ProgramSignatures.builtinIntPredicate
            (.variable origin.metavariable) } : Requirement) ∈
        result.state.requirements := by
  cases fuel with
  | zero => simp [inferMatchPatternFlatFuel] at success
  | succ fuel =>
      cases value with
      | string spelling => simp [Frontend.numericLiteralValue?] at numeric
      | decimal spelling =>
          unfold inferMatchPatternFlatFuel at success
          simp only [patternValue, literalValue, numeric, bind, Except.bind]
            at success
          simp [State.fresh, TypeSystem.InferState.fresh,
            State.addRequirementWithId] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals try cases success
          all_goals try subst result
          all_goals
            obtain ⟨patternsEq, requirementsEq⟩ :=
              unify_integerPatternMetadata_eq (by assumption)
            rw [patternsEq, requirementsEq]
            refine ⟨{
                rawValue
                targetType := .variable ⟨state.inference.next⟩
                requirement := ⟨state.nextRequirement⟩
              }, ?_⟩
            simp_all
            refine ⟨({
                metavariable := ⟨state.inference.next⟩
                span := pattern.span
                requirement := ⟨state.nextRequirement⟩
              } : IntegerPatternOrigin), ?_⟩
            simp
      | hexadecimal spelling =>
          unfold inferMatchPatternFlatFuel at success
          simp only [patternValue, literalValue, numeric, bind, Except.bind]
            at success
          simp [State.fresh, TypeSystem.InferState.fresh,
            State.addRequirementWithId] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals try cases success
          all_goals try subst result
          all_goals
            obtain ⟨patternsEq, requirementsEq⟩ :=
              unify_integerPatternMetadata_eq (by assumption)
            rw [patternsEq, requirementsEq]
            refine ⟨{
                rawValue
                targetType := .variable ⟨state.inference.next⟩
                requirement := ⟨state.nextRequirement⟩
              }, ?_⟩
            simp_all
            refine ⟨({
                metavariable := ⟨state.inference.next⟩
                span := pattern.span
                requirement := ⟨state.nextRequirement⟩
              } : IntegerPatternOrigin), ?_⟩
            simp

/-- Public-wrapper form of
`inferMatchPatternFlatFuel_integerLiteral_metadata` for a root numeric
pattern. -/
theorem inferMatchPatternFuel_integerLiteral_metadata
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {literal : Syntax.CoreLiteral} {value : Syntax.CoreLiteralValue}
    {expected : Ty} {state next : State} {typed : TypedMatchPattern}
    {rawValue : Nat}
    (patternValue : pattern.value = .literal literal)
    (literalValue : literal.value = value)
    (numeric : Frontend.numericLiteralValue? value = some rawValue)
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok (typed, next)) :
    ∃ resolution origin,
      typed.resolution = .integerLiteral value resolution ∧
      typed.requirements = [resolution.requirement] ∧
      resolution.rawValue = rawValue ∧
      resolution.targetType = .variable origin.metavariable ∧
      resolution.requirement = origin.requirement ∧
      origin.span = pattern.span ∧
      origin ∈ next.integerPatterns ∧
      ({ id := origin.requirement,
          predicate := ProgramSignatures.builtinIntPredicate
            (.variable origin.metavariable) } : Requirement) ∈
        next.requirements := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      injection success with resultEq
      cases resultEq
      exact inferMatchPatternFlatFuel_integerLiteral_metadata patternValue
        literalValue numeric flatResult

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

@[simp] private theorem fresh_requirements_eq (state : State) :
    state.fresh.2.requirements = state.requirements := by
  rfl

@[simp] private theorem restoreLexicalScope_requirements_eq
    (state : State) (scope : LexicalScope) :
    (state.restoreLexicalScope scope).requirements = state.requirements := by
  rfl

@[simp] private theorem allocateBinder_requirements_eq
    (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement) :
    (state.allocateBinder name scheme span comptime
      schemeRequirements).2.requirements = state.requirements := by
  rfl

@[simp] private theorem allocateHiddenLocal_requirements_eq (state : State) :
    state.allocateHiddenLocal.2.requirements = state.requirements := by
  rfl

@[simp] private theorem allocateExpressionId_requirements_eq (state : State) :
    state.allocateExpressionId.2.requirements = state.requirements := by
  rfl

@[simp] private theorem allocateStatementId_requirements_eq (state : State) :
    state.allocateStatementId.2.requirements = state.requirements := by
  rfl

@[simp] private theorem recordNode_requirements_eq
    (state : State) (node : Node) :
    (state.recordNode node).requirements = state.requirements := by
  rfl

private theorem pair_success_requirements_subset {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : initial.requirements ⊆ operation.2.requirements)
    (success : operation = (value, next)) :
    initial.requirements ⊆ next.requirements := by
  simpa [success] using operationSubset

private theorem pair_eq_property {alpha beta : Type} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem anchored_pair_except_property {epsilon alpha beta : Type}
    {anchor : alpha × State}
    {computation : alpha → State → Except epsilon (beta × State)}
    {initial state : State} {result : beta × State}
    (_anchorInvariant : ∀ value next,
      (Except.ok anchor : Except epsilon (alpha × State)) =
          Except.ok (value, next) →
        initial.requirements ⊆ next.requirements)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        state.requirements ⊆ next.requirements)
    (success : computation anchor.1 state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success

private theorem mem_addRequirementsWithIds
    {requirement : Requirement} {state : State}
    {predicates : List ProgramPredicate}
    (member : requirement ∈ state.requirements) :
    requirement ∈
      (state.addRequirementsWithIds predicates).2.requirements :=
  State.addRequirementsWithIds_requirements_subset state predicates member

private theorem allocateExpressionId_success_requirements_subset
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.allocateExpressionId_requirements_subset state) success

private theorem allocateStatementId_success_requirements_subset
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.allocateStatementId_requirements_subset state) success

private theorem state_fresh_success_requirements_subset
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset (State.fresh_requirements_subset state)
    success

private theorem allocateHiddenLocal_success_requirements_subset
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.allocateHiddenLocal_requirements_subset state) success

private theorem addRequirementWithId_success_requirements_subset
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.addRequirementWithId_requirements_subset state predicate) success

private theorem addRequirementsWithIds_success_requirements_subset
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.addRequirementsWithIds_requirements_subset state predicates) success

private theorem allocateBinder_success_requirements_subset
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (State.allocateBinder_requirements_subset state name scheme span comptime
      schemeRequirements) success

private theorem freshDataConstructorInstantiation_success_requirements_subset
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (freshDataConstructorInstantiation_requirements_subset dataType constructor
      state) success

private theorem freshTypes_success_requirements_subset
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    state.requirements ⊆ next.requirements :=
  pair_success_requirements_subset
    (freshTypes_requirements_subset count state) success

private theorem syntheticTuple_result_requirements_subset
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
    state.requirements ⊆ result.snd.requirements := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact List.Subset.trans
    (State.allocateExpressionId_requirements_subset state)
    (State.recordNode_requirements_subset state.allocateExpressionId.snd _)

private theorem syntheticTuple_pair_requirements_subset
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = result) :
    state.requirements ⊆ result.snd.requirements := by
  rw [← success]
  exact List.Subset.trans
    (State.allocateExpressionId_requirements_subset state)
    (State.recordNode_requirements_subset state.allocateExpressionId.snd _)

private theorem pure_pair_result_requirements_subset {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : initial.requirements ⊆ next.requirements)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    initial.requirements ⊆ result.snd.requirements := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_requirements_subset {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : initial.requirements ⊆ state.requirements)
    (success : (value, state.restoreLexicalScope scope) = result) :
    initial.requirements ⊆ result.snd.requirements := by
  rw [← success]
  exact List.Subset.trans subset
    (State.restoreLexicalScope_requirements_subset state scope)

set_option maxHeartbeats 2000000 in
private theorem inferFuel_preserves_requirements_internal :
    (∀ fuel context expression expected state,
      PreservesRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesRequirements Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesRequirements Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesRequirements Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesRequirements Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesRequirements at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_requirements_subset statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_requirements_subset (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_requirements_subset (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_requirements_subset casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_requirements_subset bodySubset (by assumption)
    all_goals try simp_all
    all_goals intro requirement member
    all_goals try solve_by_elim (maxDepth := 30)
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesRequirements at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨place, placeState⟩
    all_goals try rcases v_2 with ⟨inferred, resultState⟩
    all_goals
      have placeSubset := pair_except_property placeInduction rfl
    all_goals try have valueSubset :=
      valueInduction place v_1 inferred resultState (by assumption)
    all_goals try
      have valueSubset := anchored_pair_except_property placeInduction
        valueInduction (by assumption)
    all_goals try have valueSubset :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedSubset :=
      unify_requirements_subset (by assumption)
    all_goals simp_all
    all_goals intro requirement member
    all_goals grind
  case case67 =>
    unfold PreservesRequirements at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesRequirements at *
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
    try simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
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
      | have ih1Subset := pair_eq_property ih1
      | have ih1Subset := pair_except_property ih1 (by assumption)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2
      | have ih2Subset := pair_except_property ih2 (by assumption)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3
      | have ih3Subset := pair_except_property ih3 (by assumption)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have unifiedSubset :=
      unify_requirements_subset (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_requirements_subset (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_requirements_subset (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_requirements_subset (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_requirements_subset (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_requirements_subset (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_requirements_subset (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_requirements_subset (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_requirements_subset (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_requirements_subset (by assumption)
    all_goals try have recordSubset :=
      recordExpressionWithExpected_requirements_subset (by assumption)
    all_goals try have lambdaSubset :=
      bindLambdaParameters_requirements_subset (by assumption)
    all_goals try
      have afterLambdaSubset := List.Subset.trans lambdaSubset
        (unify_requirements_subset (by assumption))
    all_goals try have patternSubset :=
      inferMatchPatternFuel_requirements_subset (by assumption)
    all_goals try have unarySubset :=
      inferUnaryOperator_requirements_subset (by assumption)
    all_goals try have binarySubset :=
      inferBinaryOperator_requirements_subset (by assumption)
    all_goals try have selectionSubset :=
      selectFunctionCandidateFrom_requirements_subset (by assumption)
    all_goals try have expectedSubset :=
      withExpected_requirements_subset (by assumption)
    all_goals try have applicationSubset :=
      applyFunctionType_requirements_subset (by assumption)
    all_goals try have builtinSubset :=
      recordBuiltinFunctionCall_requirements_subset (by assumption)
    all_goals try simp_all
    all_goals try simp_all [State.addRequirementWithId]
    all_goals try obtain ⟨recordSubset, recordMember⟩ := recordSubset
    all_goals intro requirement member
    all_goals grind
      [inferMatchPatternFuel_requirements_subset,
        fresh_requirements_eq,
        restoreLexicalScope_requirements_eq,
        allocateBinder_requirements_eq,
        allocateHiddenLocal_requirements_eq,
        allocateExpressionId_requirements_eq,
        allocateStatementId_requirements_eq,
        recordNode_requirements_eq,
        mem_addRequirementsWithIds,
        unify_requirements_subset,
        State.addRequirementWithId_requirements_subset,
        State.addRequirementsWithIds_requirements_subset,
        freshDataConstructorInstantiation_requirements_subset,
        freshTypes_requirements_subset,
        recordExpression_requirements_subset,
        recordExpressionWithExpected_requirements_subset,
        recordSelectedCallResult_requirements_subset,
        recordSelectedCall_requirements_subset,
        recordIndirectCall_requirements_subset,
        bindLambdaParameters_requirements_subset,
        inferUnaryOperator_requirements_subset,
        inferBinaryOperator_requirements_subset,
        selectFunctionCandidateFrom_requirements_subset,
        withExpected_requirements_subset,
        applyFunctionType_requirements_subset,
      recordBuiltinFunctionCall_requirements_subset]

theorem inferExprFuel_requirements_subset
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_requirements_subset
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_requirements_subset
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_requirements_subset
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    state.requirements ⊆ result.state.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_requirements_subset
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    state.requirements ⊆ result.state.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_requirements_subset
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_requirements_subset
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_requirements_subset
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_requirements_subset
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    state.requirements ⊆ result.2.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_requirements_subset
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    state.requirements ⊆ result.2.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_requirements_subset
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    state.requirements ⊆ result.state.requirements := by
  exact inferFuel_preserves_requirements_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

private theorem addRequirementsWithIds_integerPatterns_eq
    (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.integerPatterns =
      state.integerPatterns := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [State.addRequirementsWithIds]
      exact (induction (state.addRequirementWithId predicate).2).trans rfl

private theorem commitCoercionPlan_integerPatterns_eq
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.integerPatterns =
      state.integerPatterns := by
  induction plan generalizing state with
  | nil => rfl
  | cons step plan induction =>
      simp only [commitCoercionPlan]
      exact (induction
        ((state.addRequirementWithId step.predicate).2
          |>.addRequirementsWithIds step.methodPredicates).2).trans
        (addRequirementsWithIds_integerPatterns_eq
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates |>.trans rfl)

private theorem withExpected_integerPatterns_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
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
                      exact commitCoercionPlan_integerPatterns_eq state plan

private theorem candidateWithExpected_integerPatterns_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
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
      exact withExpected_integerPatterns_eq fittedResult

private theorem fitArguments_integerPatterns_eq
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
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
              | none =>
                  simp only [fittedResult, bind, Except.bind] at success
                  change Except.ok (none : Option ArgumentFitResult) =
                    Except.ok (some result) at success
                  simp at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error => simp [tailResult] at success
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
                          have resultEq : _ = result := Option.some.inj resultEq
                          subst result
                          exact (induction (result := tail) tailResult).trans
                            (candidateWithExpected_integerPatterns_eq
                              fittedResult)

private theorem tryFunctionCandidate_integerPatterns_eq
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fittedArgumentsEq :=
    fitArguments_integerPatterns_eq (by assumption)
  all_goals try have fittedResultEq :=
    candidateWithExpected_integerPatterns_eq (by assumption)
  all_goals
    exact (addRequirementsWithIds_integerPatterns_eq _ _).trans
      (fittedResultEq.trans fittedArgumentsEq)

private theorem collectCandidateAttempts_success_integerPatterns_eq
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {state : State}
    (attemptEq : ∀ signature result,
      attempt signature = .ok (some result) →
        result.state.integerPatterns = state.integerPatterns) :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        success.attempt.state.integerPatterns = state.integerPatterns := by
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
                  exact attemptEq signature result attemptResult
              | inr member => exact induction selected member

private theorem selectFunctionCandidateFrom_integerPatterns_eq
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
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
            exact collectCandidateAttempts_success_integerPatterns_eq
              (state := state)
              (fun signature attemptResult attemptSuccess =>
                tryFunctionCandidate_integerPatterns_eq attemptSuccess)
              candidates candidate member

private theorem inferUnaryOperator_integerPatterns_eq
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    (unify_integerPatternMetadata_eq (by assumption)).1
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerPatterns_eq _ _
  all_goals grind [unify_integerPatternMetadata_eq,
    addRequirementsWithIds_integerPatterns_eq]

private theorem inferBinaryOperator_integerPatterns_eq
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedEq :=
    (unify_integerPatternMetadata_eq (by assumption)).1
  all_goals try have requirementsEq :=
    addRequirementsWithIds_integerPatterns_eq _ _
  all_goals grind [unify_integerPatternMetadata_eq,
    addRequirementsWithIds_integerPatterns_eq]

private theorem attachExpressionCoercions_integerPatterns_eq
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).integerPatterns =
      state.integerPatterns := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction
        (state.modifyExpressionNode entry.expression fun node => {
          node with
          type := entry.coercions.foldl (fun _ step => step.target) node.type
          requirements :=
            node.requirements ++ coercionRequirements entry.coercions
          coercions := node.coercions ++ entry.coercions
        })).trans rfl

private theorem recordExpression_integerPatterns_eq
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    {localSchemeInstantiationStart : Option Nat} :
    (recordExpression source expression form requirements coercions state
      localSchemeInstantiationStart).2.integerPatterns =
      state.integerPatterns := by
  rfl

@[simp] private theorem allocateExpressionId_integerPatterns_eq (state : State) :
    state.allocateExpressionId.2.integerPatterns = state.integerPatterns := by
  rfl

private theorem recordExpressionWithExpected_integerPatterns_eq
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.integerPatterns = state.integerPatterns := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok (recordExpression source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state localSchemeInstantiationStart) =
          Except.ok result at success
      injection success with resultEq
      subst result
      exact (recordExpression_integerPatterns_eq source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state).trans
          (withExpected_integerPatterns_eq fittedResult)

private theorem recordSelectedCallResult_integerPatterns_eq
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.integerPatterns = state.integerPatterns := by
  unfold recordSelectedCallResult
  rw [recordExpression_integerPatterns_eq,
    recordExpression_integerPatterns_eq]
  exact (attachExpressionCoercions_integerPatterns_eq state
    attempt.argumentCoercions)

private theorem recordSelectedCall_integerPatterns_eq
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.integerPatterns =
      attempt.state.integerPatterns := by
  exact recordSelectedCallResult_integerPatterns_eq source callee name
    arguments attempt attempt.result [] attempt.state

private theorem recordIndirectCall_integerPatterns_eq
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.integerPatterns =
      result.state.integerPatterns := by
  unfold recordIndirectCall
  exact recordExpression_integerPatterns_eq _ _ _ _ _ _

private theorem applyFunctionType_integerPatterns_eq
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.integerPatterns = state.integerPatterns := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error => simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error => simp [resultResult] at success
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
              exact (withExpected_integerPatterns_eq resultResult).trans
                (withExpected_integerPatterns_eq argumentResult)
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error => simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error => simp [resultResult] at success
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
              have freshEq : freshState.integerPatterns =
                  state.integerPatterns := by
                have projected := congrArg
                  (fun result : Ty × State => result.2.integerPatterns)
                  freshResultEq
                simpa [State.fresh] using projected.symm
              exact (withExpected_integerPatterns_eq resultResult).trans
                ((unify_integerPatternMetadata_eq unifyResult).1.trans freshEq)

private theorem bindLambdaParameters_integerPatterns_eq
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    result.2.2.integerPatterns = state.integerPatterns := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailEq := induction _ _ _ (by assumption)
            simpa [State.fresh, State.allocateBinder] using tailEq
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
                have tailEq := induction _ _ _ (by assumption)
                simpa [State.allocateBinder] using tailEq

private theorem unifyBuiltinFunctionArgumentsEqual_integerPatterns_eq
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.integerPatterns = state.integerPatterns := by
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
          | ok unified =>
              simp only [unifyResult, bind, Except.bind] at success
              exact (induction success).trans
                (unify_integerPatternMetadata_eq unifyResult).1

private theorem recordBuiltinFunctionCall_integerPatterns_eq
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.integerPatterns = state.integerPatterns := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have argumentsEq :=
    unifyBuiltinFunctionArgumentsEqual_integerPatterns_eq (by assumption)
  all_goals try have unifiedEq :=
    (unify_integerPatternMetadata_eq (by assumption)).1
  all_goals try have recordedEq :=
    recordExpression_integerPatterns_eq _ _ _ _ _ _
  all_goals try
    rw [recordExpression_integerPatterns_eq,
      recordExpression_integerPatterns_eq,
      allocateExpressionId_integerPatterns_eq]
  all_goals first
    | exact unifiedEq.trans argumentsEq
    | exact argumentsEq

@[simp] private theorem stateFresh_integerPatterns_eq (state : State) :
    state.fresh.2.integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem withLocals_integerPatterns_eq
    (state : State) (locals : TypeSystem.Environment) :
    (state.withLocals locals).integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem restoreLexicalScope_integerPatterns_eq
    (state : State) (scope : LexicalScope) :
    (state.restoreLexicalScope scope).integerPatterns =
      state.integerPatterns := by
  rfl

@[simp] private theorem allocateBinder_integerPatterns_eq
    (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement) :
    (state.allocateBinder name scheme span comptime
      schemeRequirements).2.integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem allocateHiddenLocal_integerPatterns_eq
    (state : State) :
    state.allocateHiddenLocal.2.integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem allocateStatementId_integerPatterns_eq
    (state : State) :
    state.allocateStatementId.2.integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem recordNode_integerPatterns_eq
    (state : State) (node : Node) :
    (state.recordNode node).integerPatterns = state.integerPatterns := by
  rfl

@[simp] private theorem addRequirementWithId_integerPatterns_eq
    (state : State) (predicate : ProgramPredicate) :
    (state.addRequirementWithId predicate).2.integerPatterns =
      state.integerPatterns := by
  rfl

private theorem integerPatterns_subset_of_eq {before after : State}
    (equal : after.integerPatterns = before.integerPatterns) :
    before.integerPatterns ⊆ after.integerPatterns := by
  rw [equal]
  exact fun _ member => member

private theorem pair_success_integerPatterns_subset {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationEq : operation.2.integerPatterns = initial.integerPatterns)
    (success : operation = (value, next)) :
    initial.integerPatterns ⊆ next.integerPatterns := by
  rw [success] at operationEq
  exact integerPatterns_subset_of_eq operationEq

private theorem anchored_pair_except_integerPatterns_subset
    {epsilon alpha beta : Type}
    {anchor : alpha × State}
    {computation : alpha → State → Except epsilon (beta × State)}
    {initial state : State} {result : beta × State}
    (_anchorInvariant : ∀ value next,
      (Except.ok anchor : Except epsilon (alpha × State)) =
          Except.ok (value, next) →
        initial.integerPatterns ⊆ next.integerPatterns)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        state.integerPatterns ⊆ next.integerPatterns)
    (success : computation anchor.1 state = .ok result) :
    state.integerPatterns ⊆ result.2.integerPatterns := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success

private theorem syntheticTuple_result_integerPatterns_subset
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
    state.integerPatterns ⊆ result.2.integerPatterns := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact fun _ member => member

private theorem syntheticTuple_pair_integerPatterns_subset
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = result) :
    state.integerPatterns ⊆ result.2.integerPatterns := by
  rw [← success]
  exact fun _ member => member

private theorem pure_pair_result_integerPatterns_subset {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : initial.integerPatterns ⊆ next.integerPatterns)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    initial.integerPatterns ⊆ result.2.integerPatterns := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_integerPatterns_subset {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : initial.integerPatterns ⊆ state.integerPatterns)
    (success : (value, state.restoreLexicalScope scope) = result) :
    initial.integerPatterns ⊆ result.2.integerPatterns := by
  rw [← success]
  exact subset

set_option maxHeartbeats 2000000 in
private theorem inferFuel_preserves_integerPatterns_internal :
    (∀ fuel context expression expected state,
      PreservesIntegerPatterns Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesIntegerPatterns Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesIntegerPatterns Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesIntegerPatterns BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesIntegerPatterns StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesIntegerPatterns InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesIntegerPatterns Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesIntegerPatterns Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesIntegerPatterns (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesIntegerPatterns Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesIntegerPatterns MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesIntegerPatterns Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesIntegerPatterns Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesIntegerPatterns Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesIntegerPatterns BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesIntegerPatterns StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesIntegerPatterns InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesIntegerPatterns Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesIntegerPatterns Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesIntegerPatterns (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesIntegerPatterns Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesIntegerPatterns MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesIntegerPatterns at *
    intro result success
    have statementIdSubset := pair_success_integerPatterns_subset
      (operation := state.allocateStatementId) (by rfl) statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_integerPatterns_subset (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_integerPatterns_subset (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_integerPatterns_subset casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_integerPatterns_subset bodySubset (by assumption)
    all_goals try simp_all [State.recordNode, State.allocateHiddenLocal]
    all_goals
      have initialSubset :
          state.integerPatterns ⊆ stateAfterId.integerPatterns :=
        pair_success_integerPatterns_subset
          (operation := state.allocateStatementId) (value := id)
          (next := stateAfterId) (initial := state) (by rfl) statementIdEq
    all_goals intro origin member
    all_goals try solve_by_elim (maxDepth := 30)
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesIntegerPatterns at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨place, placeState⟩
    all_goals try rcases v_2 with ⟨inferred, resultState⟩
    all_goals have placeSubset := pair_except_property placeInduction rfl
    all_goals try have valueSubset :=
      valueInduction place v_1 inferred resultState (by assumption)
    all_goals try
      have valueSubset := anchored_pair_except_integerPatterns_subset
        placeInduction
        valueInduction (by assumption)
    all_goals try have valueSubset :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try
      have unifiedSubset := integerPatterns_subset_of_eq
        ((unify_integerPatternMetadata_eq (by assumption)).1)
    all_goals simp_all
    all_goals intro origin member
    all_goals grind
  case case67 =>
    unfold PreservesIntegerPatterns at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesIntegerPatterns at *
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
    try simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
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
      | have ih1Subset := pair_eq_property ih1
      | have ih1Subset := pair_except_property ih1 (by assumption)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2
      | have ih2Subset := pair_except_property ih2 (by assumption)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3
      | have ih3Subset := pair_except_property ih3 (by assumption)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try
      have unifiedSubset := integerPatterns_subset_of_eq
        ((unify_integerPatternMetadata_eq (by assumption)).1)
    all_goals try
      have recordSubset := integerPatterns_subset_of_eq
        (recordExpressionWithExpected_integerPatterns_eq (by assumption))
    all_goals try
      have lambdaSubset := integerPatterns_subset_of_eq
        (bindLambdaParameters_integerPatterns_eq (by assumption))
    all_goals try have patternSubset :=
      inferMatchPatternFuel_integerPatterns_subset (by assumption)
    all_goals try
      have unarySubset := integerPatterns_subset_of_eq
        (inferUnaryOperator_integerPatterns_eq (by assumption))
    all_goals try
      have binarySubset := integerPatterns_subset_of_eq
        (inferBinaryOperator_integerPatterns_eq (by assumption))
    all_goals try
      have selectionSubset := integerPatterns_subset_of_eq
        (selectFunctionCandidateFrom_integerPatterns_eq (by assumption))
    all_goals try
      have expectedSubset := integerPatterns_subset_of_eq
        (withExpected_integerPatterns_eq (by assumption))
    all_goals try
      have applicationSubset := integerPatterns_subset_of_eq
        (applyFunctionType_integerPatterns_eq (by assumption))
    all_goals try
      have builtinSubset := integerPatterns_subset_of_eq
        (recordBuiltinFunctionCall_integerPatterns_eq (by assumption))
    all_goals try simp_all
    all_goals intro origin member
    all_goals grind
      [inferMatchPatternFuel_integerPatterns_subset,
        unify_integerPatternMetadata_eq,
        stateFresh_integerPatterns_eq,
        withLocals_integerPatterns_eq,
        restoreLexicalScope_integerPatterns_eq,
        allocateBinder_integerPatterns_eq,
        allocateHiddenLocal_integerPatterns_eq,
        allocateExpressionId_integerPatterns_eq,
        allocateStatementId_integerPatterns_eq,
        recordNode_integerPatterns_eq,
        addRequirementWithId_integerPatterns_eq,
        freshTypes_integerPatterns_eq,
        freshDataConstructorInstantiation_integerPatterns_eq,
        addRequirementsWithIds_integerPatterns_eq,
        recordExpression_integerPatterns_eq,
        recordExpressionWithExpected_integerPatterns_eq,
        recordSelectedCallResult_integerPatterns_eq,
        recordSelectedCall_integerPatterns_eq,
        recordIndirectCall_integerPatterns_eq,
        bindLambdaParameters_integerPatterns_eq,
        inferUnaryOperator_integerPatterns_eq,
        inferBinaryOperator_integerPatterns_eq,
        selectFunctionCandidateFrom_integerPatterns_eq,
        withExpected_integerPatterns_eq,
        applyFunctionType_integerPatterns_eq,
        recordBuiltinFunctionCall_integerPatterns_eq]

/-- Whole-block inference retains every numeric-pattern origin already present
in its input state. -/
theorem inferStatementsFuel_integerPatterns_subset
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    state.integerPatterns ⊆ result.state.integerPatterns := by
  exact inferFuel_preserves_integerPatterns_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

/-- Match-arm inference retains the input origin ledger while carrying every
origin introduced by an earlier arm through later bodies and cases. -/
theorem inferMatchCasesFuel_integerPatterns_subset
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    state.integerPatterns ⊆ result.state.integerPatterns := by
  exact inferFuel_preserves_integerPatterns_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

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
