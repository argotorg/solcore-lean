import Solcore.Frontend.SourceInference.Types

/-! Allocation and lexical-restoration laws for the typed source state. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.State

/-- Every recorded source node was allocated strictly before the next
declaration-local occurrence identity.  This is the minimal freshness fact
needed to distinguish a traversal's pre-existing nodes from nodes allocated by
that traversal. -/
def NodesBelowNextOccurrence (state : State) : Prop :=
  ∀ node ∈ state.nodes,
    node.occurrenceId.index < state.nextOccurrence

/-- The part of source-inference state evolution needed to preserve occurrence
allocation safety.  This deliberately says nothing about exact node payloads:
`attachExpressionCoercions` may refine freshly recorded expression nodes while
still preserving their identities and the allocation bound. -/
structure OccurrenceBoundExtends (before after : State) : Prop where
  nextOccurrence_le : before.nextOccurrence ≤ after.nextOccurrence
  nodesBelowNextOccurrence :
    before.NodesBelowNextOccurrence → after.NodesBelowNextOccurrence

namespace OccurrenceBoundExtends

/-- Every state trivially extends its own occurrence-allocation bound. -/
theorem refl (state : State) : state.OccurrenceBoundExtends state :=
  ⟨Nat.le_refl _, fun below => below⟩

/-- Equal node tables and equal occurrence counters are sufficient for an
occurrence-bound extension, even when unrelated state fields change. -/
theorem of_nodes_eq_nextOccurrence_eq {before after : State}
    (nodesEq : after.nodes = before.nodes)
    (nextEq : after.nextOccurrence = before.nextOccurrence) :
    before.OccurrenceBoundExtends after := by
  constructor
  · rw [nextEq]
    exact Nat.le_refl _
  · intro below node member
    rw [nodesEq] at member
    rw [nextEq]
    exact below node member

/-- Occurrence-bound extension composes across sequential inference steps. -/
theorem trans {first second third : State}
    (left : first.OccurrenceBoundExtends second)
    (right : second.OccurrenceBoundExtends third) :
    first.OccurrenceBoundExtends third :=
  ⟨Nat.le_trans left.nextOccurrence_le right.nextOccurrence_le,
    fun below => right.nodesBelowNextOccurrence
      (left.nodesBelowNextOccurrence below)⟩

end OccurrenceBoundExtends

private theorem map_mapIdx {α β γ : Type} (items : List α)
    (indexed : Nat → α → β)
    (project : β → γ) :
    (items.mapIdx indexed).map project =
      items.mapIdx fun index item => project (indexed index item) := by
  induction items generalizing indexed with
  | nil => rfl
  | cons item rest induction =>
      simp only [List.mapIdx_cons, List.map_cons]
      exact congrArg (project (indexed 0 item) :: ·)
        (induction (fun index item => indexed (index + 1) item))

@[simp] theorem initial_owner (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).owner = owner := by
  rfl

@[simp] theorem initial_inputs_eq_localBinders
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (inputComptime : List Bool) :
    (initial owner locals inputComptime).inputs =
      (initial owner locals inputComptime).localBinders := by
  rfl

/-- Initial input names are exactly the source parameter names, in order. -/
theorem initial_input_names (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).inputs.map (fun input => input.name) =
      locals.map (fun entry => entry.1) := by
  rw [initial_inputs_definition, map_mapIdx]
  induction locals with
  | nil => rfl
  | cons entry rest induction => simp [List.mapIdx_cons, induction]

/-- Initial input staging markers are the supplied markers, defaulting missing
entries to `false`, in parameter order. -/
theorem initial_input_comptime (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).inputs.map
        (fun input => input.comptime) =
      locals.mapIdx fun index _ => inputComptime.getD index false := by
  rw [initial_inputs_definition, map_mapIdx]

/-- When the signature supplies one staging marker per parameter, the initial
input binders retain that list exactly. -/
theorem initial_input_comptime_eq (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool)
    (lengthEq : locals.length = inputComptime.length) :
    (initial owner locals inputComptime).inputs.map
        (fun input => input.comptime) = inputComptime := by
  rw [initial_input_comptime]
  induction locals generalizing inputComptime with
  | nil =>
      cases inputComptime with
      | nil => rfl
      | cons marker rest => simp at lengthEq
  | cons entry locals induction =>
      cases inputComptime with
      | nil => simp at lengthEq
      | cons marker rest =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEq
          simp only [List.mapIdx_cons, List.getD_cons_zero,
            List.getD_cons_succ]
          exact congrArg (marker :: ·) (induction rest lengthEq)

@[simp] theorem initial_header (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).header = {
      owner
      inputs := (initial owner locals inputComptime).inputs
    } := by
  rfl

/-- An initial inference state has no recorded occurrence nodes. -/
theorem initial_nodesBelowNextOccurrence (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (initial owner locals inputComptime).NodesBelowNextOccurrence := by
  intro node member
  simp [initial] at member

@[simp] theorem fresh_header (state : State) :
    state.fresh.2.header = state.header := by
  rfl

/-- Allocating a type metavariable leaves the occurrence stream unchanged. -/
theorem fresh_preserves_nodesBelowNextOccurrence
    (state : State) (below : state.NodesBelowNextOccurrence) :
    state.fresh.2.NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem withLocals_header (state : State)
    (locals : TypeSystem.Environment) :
    (state.withLocals locals).header = state.header := by
  rfl

/-- Replacing the compatibility-only local environment does not affect
occurrence allocation. -/
theorem withLocals_preserves_nodesBelowNextOccurrence
    (state : State) (locals : TypeSystem.Environment)
    (below : state.NodesBelowNextOccurrence) :
    (state.withLocals locals).NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem restoreLexicalScope_header (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).header = state.header := by
  rfl

/-- Restoring lexical names preserves all globally allocated occurrences. -/
theorem restoreLexicalScope_preserves_nodesBelowNextOccurrence
    (state : State) (scope : LexicalScope)
    (below : state.NodesBelowNextOccurrence) :
    (state.restoreLexicalScope scope).NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem allocateBinder_header (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (schemeRequirements : List LocalSchemeRequirement) :
    (state.allocateBinder name scheme span comptime schemeRequirements).2.header =
      state.header := by
  rfl

/-- Allocating a visible local binder does not affect occurrence allocation. -/
theorem allocateBinder_preserves_nodesBelowNextOccurrence
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement)
    (below : state.NodesBelowNextOccurrence) :
    (state.allocateBinder name scheme span comptime schemeRequirements).2
      |>.NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem allocateHiddenLocal_header (state : State) :
    state.allocateHiddenLocal.2.header = state.header := by
  rfl

/-- Reserving a hidden local identity does not affect occurrence allocation. -/
theorem allocateHiddenLocal_preserves_nodesBelowNextOccurrence
    (state : State) (below : state.NodesBelowNextOccurrence) :
    state.allocateHiddenLocal.2.NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem allocateExpressionId_header (state : State) :
    state.allocateExpressionId.2.header = state.header := by
  rfl

/-- Reserving an expression occurrence advances the upper bound while leaving
the existing node table unchanged. -/
theorem allocateExpressionId_preserves_nodesBelowNextOccurrence
    (state : State) (below : state.NodesBelowNextOccurrence) :
    state.allocateExpressionId.2.NodesBelowNextOccurrence := by
  intro node member
  change node.occurrenceId.index < state.nextOccurrence + 1
  exact Nat.lt_succ_of_lt (below node member)

@[simp] theorem allocateStatementId_header (state : State) :
    state.allocateStatementId.2.header = state.header := by
  rfl

/-- Reserving a statement occurrence advances the shared upper bound while
leaving the existing node table unchanged. -/
theorem allocateStatementId_preserves_nodesBelowNextOccurrence
    (state : State) (below : state.NodesBelowNextOccurrence) :
    state.allocateStatementId.2.NodesBelowNextOccurrence := by
  intro node member
  change node.occurrenceId.index < state.nextOccurrence + 1
  exact Nat.lt_succ_of_lt (below node member)

@[simp] theorem recordNode_header (state : State) (node : Node) :
    (state.recordNode node).header = state.header := by
  rfl

/-- Recording one already allocated node preserves the allocation bound when
the new node lies below the current next occurrence. -/
theorem recordNode_preserves_nodesBelowNextOccurrence
    (state : State) (node : Node)
    (below : state.NodesBelowNextOccurrence)
    (nodeBelow : node.occurrenceId.index < state.nextOccurrence) :
    (state.recordNode node).NodesBelowNextOccurrence := by
  intro current member
  change current ∈ state.nodes ++ [node] at member
  rcases List.mem_append.mp member with member | member
  · exact below current member
  · simp only [List.mem_singleton] at member
    subst current
    exact nodeBelow

/-- Recording a node extends the node table by an exact suffix. -/
theorem recordNode_nodesPrefix (state : State) (node : Node) :
    state.nodes <+: (state.recordNode node).nodes := by
  exact List.prefix_append state.nodes [node]

@[simp] theorem modifyExpressionNode_header (state : State)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    (state.modifyExpressionNode id modify).header = state.header := by
  rfl

/-- Updating expression payload preserves occurrence identities and therefore
the allocation bound. -/
theorem modifyExpressionNode_preserves_nodesBelowNextOccurrence
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (below : state.NodesBelowNextOccurrence) :
    (state.modifyExpressionNode id modify).NodesBelowNextOccurrence := by
  intro current member
  change current ∈ state.nodes.map (fun
    | .expression node =>
        if node.id = id then
          .expression { modify node with id }
        else
          .expression node
    | .statement node => .statement node) at member
  rcases List.mem_map.mp member with
    ⟨original, originalMember, currentEq⟩
  cases original with
  | statement node =>
      simp only at currentEq
      subst current
      exact below (.statement node) originalMember
  | expression node =>
      simp only at currentEq
      split at currentEq
      · rename_i idEq
        subst id
        subst current
        exact below (.expression node) originalMember
      · subst current
        exact below (.expression node) originalMember

private theorem map_modifyExpressionNode_eq_self_of_fresh
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (cutoff : Nat) (idFresh : cutoff ≤ id.occurrence.index) :
    ∀ nodes : List Node,
      (∀ node ∈ nodes, node.occurrenceId.index < cutoff) →
      nodes.map (fun
        | .expression node =>
            if node.id = id then
              .expression { modify node with id }
            else
              .expression node
        | .statement node => .statement node) = nodes
  | [], _ => rfl
  | .expression node :: nodes, below => by
      have headBelow : node.id.occurrence.index < cutoff := by
        simpa [Node.occurrenceId, Node.id, NodeId.occurrenceId] using
          below (.expression node) (by simp)
      have idNe : node.id ≠ id := by
        intro idEq
        rw [idEq] at headBelow
        exact (Nat.not_lt_of_ge idFresh) headBelow
      have tailBelow :
          ∀ tail ∈ nodes, tail.occurrenceId.index < cutoff := by
        intro tail member
        exact below tail (by simp [member])
      simp only [List.map_cons]
      rw [if_neg idNe]
      exact congrArg (.expression node :: ·)
        (map_modifyExpressionNode_eq_self_of_fresh id modify cutoff idFresh
          nodes tailBelow)
  | .statement node :: nodes, below => by
      have tailBelow :
          ∀ tail ∈ nodes, tail.occurrenceId.index < cutoff := by
        intro tail member
        exact below tail (by simp [member])
      simp only [List.map_cons]
      exact congrArg (.statement node :: ·)
        (map_modifyExpressionNode_eq_self_of_fresh id modify cutoff idFresh
          nodes tailBelow)

/-- Updating an expression whose identity is at or above a cutoff leaves an
older bounded node prefix byte-for-byte unchanged. -/
theorem modifyExpressionNode_preserves_nodesPrefix_of_fresh
    (state : State) (baseNodes : List Node) (cutoff : Nat)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (nodesPrefix : baseNodes <+: state.nodes)
    (baseBelow :
      ∀ node ∈ baseNodes, node.occurrenceId.index < cutoff)
    (idFresh : cutoff ≤ id.occurrence.index) :
    baseNodes <+: (state.modifyExpressionNode id modify).nodes := by
  let update : Node → Node := fun
    | .expression node =>
        if node.id = id then
          .expression { modify node with id }
        else
          .expression node
    | .statement node => .statement node
  have baseUnchanged : baseNodes.map update = baseNodes := by
    exact map_modifyExpressionNode_eq_self_of_fresh id modify cutoff idFresh
      baseNodes (by
        intro node member
        exact baseBelow node member)
  rcases nodesPrefix with ⟨suffix, stateNodes⟩
  refine ⟨suffix.map update, ?_⟩
  change baseNodes ++ suffix.map update = state.nodes.map update
  rw [← stateNodes, List.map_append, baseUnchanged]

@[simp] theorem modifyStatementNode_header (state : State)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    (state.modifyStatementNode id modify).header = state.header := by
  rfl

/-- Updating statement payload preserves occurrence identities and therefore
the allocation bound. -/
theorem modifyStatementNode_preserves_nodesBelowNextOccurrence
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (below : state.NodesBelowNextOccurrence) :
    (state.modifyStatementNode id modify).NodesBelowNextOccurrence := by
  intro current member
  change current ∈ state.nodes.map (fun
    | .expression node => .expression node
    | .statement node =>
        if node.id = id then
          .statement { modify node with id }
        else
          .statement node) at member
  rcases List.mem_map.mp member with
    ⟨original, originalMember, currentEq⟩
  cases original with
  | expression node =>
      simp only at currentEq
      subst current
      exact below (.expression node) originalMember
  | statement node =>
      simp only at currentEq
      split at currentEq
      · rename_i idEq
        subst id
        subst current
        exact below (.statement node) originalMember
      · subst current
        exact below (.statement node) originalMember

@[simp] theorem addRequirementWithId_header (state : State)
    (predicate : ProgramPredicate) :
    (state.addRequirementWithId predicate).2.header = state.header := by
  rfl

/-- Requirement allocation is independent of occurrence allocation. -/
theorem addRequirementWithId_preserves_nodesBelowNextOccurrence
    (state : State) (predicate : ProgramPredicate)
    (below : state.NodesBelowNextOccurrence) :
    (state.addRequirementWithId predicate).2.NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

/-- Adding one requirement is independent of occurrence allocation. -/
theorem addRequirement_preserves_nodesBelowNextOccurrence
    (state : State) (predicate : ProgramPredicate)
    (below : state.NodesBelowNextOccurrence) :
    (state.addRequirement predicate).NodesBelowNextOccurrence := by
  exact addRequirementWithId_preserves_nodesBelowNextOccurrence
    state predicate below

@[simp] theorem addRequirementsWithIds_header (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.header = state.header := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simpa [addRequirementsWithIds] using
        induction (state.addRequirementWithId predicate).2

/-- Allocating a sequence of requirement identities leaves the occurrence
table and its upper bound unchanged. -/
theorem addRequirementsWithIds_preserves_nodesBelowNextOccurrence
    (state : State) (predicates : List ProgramPredicate)
    (below : state.NodesBelowNextOccurrence) :
    (state.addRequirementsWithIds predicates).2.NodesBelowNextOccurrence := by
  induction predicates generalizing state with
  | nil => simpa [addRequirementsWithIds] using below
  | cons predicate rest induction =>
      simp only [addRequirementsWithIds]
      exact induction (state.addRequirementWithId predicate).2
        (addRequirementWithId_preserves_nodesBelowNextOccurrence
          state predicate below)

/-- Adding a sequence of requirements is independent of occurrence
allocation. -/
theorem addRequirements_preserves_nodesBelowNextOccurrence
    (state : State) (predicates : List ProgramPredicate)
    (below : state.NodesBelowNextOccurrence) :
    (state.addRequirements predicates).NodesBelowNextOccurrence := by
  exact addRequirementsWithIds_preserves_nodesBelowNextOccurrence
    state predicates below

@[simp] theorem addRequirementsWithIds_nodes (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.nodes = state.nodes := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [State.addRequirementsWithIds]
      exact induction (state.addRequirementWithId predicate).2

@[simp] theorem addRequirementsWithIds_nextOccurrence (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.nextOccurrence =
      state.nextOccurrence := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [State.addRequirementsWithIds]
      exact induction (state.addRequirementWithId predicate).2

@[simp] theorem addRequirements_nodes (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirements predicates).nodes = state.nodes :=
  addRequirementsWithIds_nodes state predicates

@[simp] theorem addRequirements_nextOccurrence (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirements predicates).nextOccurrence =
      state.nextOccurrence :=
  addRequirementsWithIds_nextOccurrence state predicates

@[simp] theorem markDirectCallRequirements_header (state : State)
    (requirements : List RequirementId) :
    (state.markDirectCallRequirements requirements).header = state.header := by
  rfl

/-- Marking requirement provenance changes no occurrence state. -/
theorem markDirectCallRequirements_preserves_nodesBelowNextOccurrence
    (state : State) (requirements : List RequirementId)
    (below : state.NodesBelowNextOccurrence) :
    (state.markDirectCallRequirements requirements).NodesBelowNextOccurrence := by
  change state.NodesBelowNextOccurrence
  exact below

@[simp] theorem allocateBinder_id (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan) :
    (state.allocateBinder name scheme span).1.id = {
      owner := state.owner
      binderIndex := state.nextLocal
    } := by
  rfl

@[simp] theorem allocateBinder_nextLocal (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan) :
    (state.allocateBinder name scheme span).2.nextLocal = state.nextLocal + 1 := by
  rfl

@[simp] theorem allocateExpressionId_value (state : State) :
    (state.allocateExpressionId).1 =
      ⟨{ owner := state.owner, index := state.nextOccurrence }⟩ := by
  rfl

@[simp] theorem allocateStatementId_value (state : State) :
    (state.allocateStatementId).1 =
      ⟨{ owner := state.owner, index := state.nextOccurrence }⟩ := by
  rfl

@[simp] theorem allocateExpressionId_nextOccurrence (state : State) :
    (state.allocateExpressionId).2.nextOccurrence =
      state.nextOccurrence + 1 := by
  rfl

@[simp] theorem allocateExpressionId_nodes (state : State) :
    (state.allocateExpressionId).2.nodes = state.nodes := by
  rfl

@[simp] theorem allocateStatementId_nextOccurrence (state : State) :
    (state.allocateStatementId).2.nextOccurrence =
      state.nextOccurrence + 1 := by
  rfl

@[simp] theorem allocateStatementId_nodes (state : State) :
    (state.allocateStatementId).2.nodes = state.nodes := by
  rfl

/-- The freshly reserved expression identity is immediately below the
advanced occurrence bound. -/
@[simp] theorem allocateExpressionId_index_lt_nextOccurrence (state : State) :
    (state.allocateExpressionId).1.occurrence.index <
      (state.allocateExpressionId).2.nextOccurrence := by
  change state.nextOccurrence < state.nextOccurrence + 1
  exact Nat.lt_succ_self state.nextOccurrence

/-- The freshly reserved statement identity is immediately below the shared
advanced occurrence bound. -/
@[simp] theorem allocateStatementId_index_lt_nextOccurrence (state : State) :
    (state.allocateStatementId).1.occurrence.index <
      (state.allocateStatementId).2.nextOccurrence := by
  change state.nextOccurrence < state.nextOccurrence + 1
  exact Nat.lt_succ_self state.nextOccurrence

@[simp] theorem restoreLexicalScope_nextLocal (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).nextLocal = state.nextLocal := by
  rfl

@[simp] theorem restoreLexicalScope_nextOccurrence (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).nextOccurrence = state.nextOccurrence := by
  rfl

@[simp] theorem restoreLexicalScope_nodes (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).nodes = state.nodes := by
  rfl

@[simp] theorem restoreLexicalScope_requirements (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).requirements = state.requirements := by
  rfl

@[simp] theorem recordNode_nodes (state : State) (node : Node) :
    (state.recordNode node).nodes = state.nodes ++ [node] := by
  rfl

@[simp] theorem recordNode_nextOccurrence (state : State) (node : Node) :
    (state.recordNode node).nextOccurrence = state.nextOccurrence := by
  rfl

@[simp] theorem modifyExpressionNode_nextOccurrence
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    (state.modifyExpressionNode id modify).nextOccurrence =
      state.nextOccurrence := by
  rfl

@[simp] theorem modifyStatementNode_nextOccurrence
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    (state.modifyStatementNode id modify).nextOccurrence =
      state.nextOccurrence := by
  rfl

namespace OccurrenceBoundExtends

/-- Type-metavariable allocation is an occurrence-bound extension. -/
theorem fresh (state : State) :
    state.OccurrenceBoundExtends state.fresh.2 :=
  ⟨Nat.le_refl _, fresh_preserves_nodesBelowNextOccurrence state⟩

/-- Compatibility-local replacement is an occurrence-bound extension. -/
theorem withLocals (state : State) (locals : TypeSystem.Environment) :
    state.OccurrenceBoundExtends (state.withLocals locals) :=
  ⟨Nat.le_refl _,
    withLocals_preserves_nodesBelowNextOccurrence state locals⟩

/-- Lexical restoration is an occurrence-bound extension. -/
theorem restoreLexicalScope (state : State) (scope : LexicalScope) :
    state.OccurrenceBoundExtends (state.restoreLexicalScope scope) :=
  ⟨Nat.le_refl _,
    restoreLexicalScope_preserves_nodesBelowNextOccurrence state scope⟩

/-- Visible-binder allocation is an occurrence-bound extension. -/
theorem allocateBinder (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (schemeRequirements : List LocalSchemeRequirement) :
    state.OccurrenceBoundExtends
      (state.allocateBinder name scheme span comptime schemeRequirements).2 :=
  ⟨Nat.le_refl _, allocateBinder_preserves_nodesBelowNextOccurrence
    state name scheme span comptime schemeRequirements⟩

/-- Hidden-local allocation is an occurrence-bound extension. -/
theorem allocateHiddenLocal (state : State) :
    state.OccurrenceBoundExtends state.allocateHiddenLocal.2 :=
  ⟨Nat.le_refl _, allocateHiddenLocal_preserves_nodesBelowNextOccurrence state⟩

/-- Expression-identity allocation advances the occurrence bound. -/
theorem allocateExpressionId (state : State) :
    state.OccurrenceBoundExtends state.allocateExpressionId.2 := by
  constructor
  · change state.nextOccurrence ≤ state.nextOccurrence + 1
    exact Nat.le_succ _
  · exact allocateExpressionId_preserves_nodesBelowNextOccurrence state

/-- Statement-identity allocation advances the occurrence bound. -/
theorem allocateStatementId (state : State) :
    state.OccurrenceBoundExtends state.allocateStatementId.2 := by
  constructor
  · change state.nextOccurrence ≤ state.nextOccurrence + 1
    exact Nat.le_succ _
  · exact allocateStatementId_preserves_nodesBelowNextOccurrence state

/-- Recording a previously allocated node extends the occurrence bound. -/
theorem recordNode (state : State) (node : Node)
    (nodeBelow : node.occurrenceId.index < state.nextOccurrence) :
    state.OccurrenceBoundExtends (state.recordNode node) :=
  ⟨Nat.le_refl _, fun below =>
    recordNode_preserves_nodesBelowNextOccurrence state node below nodeBelow⟩

/-- Expression-node payload refinement preserves the occurrence bound. -/
theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    state.OccurrenceBoundExtends (state.modifyExpressionNode id modify) :=
  ⟨Nat.le_refl _, fun below =>
    modifyExpressionNode_preserves_nodesBelowNextOccurrence state id modify below⟩

/-- Statement-node payload refinement preserves the occurrence bound. -/
theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    state.OccurrenceBoundExtends (state.modifyStatementNode id modify) :=
  ⟨Nat.le_refl _, fun below =>
    modifyStatementNode_preserves_nodesBelowNextOccurrence state id modify below⟩

/-- Single requirement allocation is independent of occurrence allocation. -/
theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    state.OccurrenceBoundExtends
      (state.addRequirementWithId predicate).2 :=
  ⟨Nat.le_refl _, fun below =>
    addRequirementWithId_preserves_nodesBelowNextOccurrence
      state predicate below⟩

/-- Adding one requirement is independent of occurrence allocation. -/
theorem addRequirement (state : State) (predicate : ProgramPredicate) :
    state.OccurrenceBoundExtends (state.addRequirement predicate) :=
  ⟨Nat.le_refl _, fun below =>
    addRequirement_preserves_nodesBelowNextOccurrence state predicate below⟩

/-- Requirement-list allocation is independent of occurrence allocation. -/
theorem addRequirementsWithIds (state : State)
    (predicates : List ProgramPredicate) :
    state.OccurrenceBoundExtends
      (state.addRequirementsWithIds predicates).2 := by
  induction predicates generalizing state with
  | nil => exact .refl state
  | cons predicate rest induction =>
      simpa only [State.addRequirementsWithIds] using
        (addRequirementWithId state predicate).trans
          (induction (state.addRequirementWithId predicate).2)

/-- Adding requirements is independent of occurrence allocation. -/
theorem addRequirements (state : State) (predicates : List ProgramPredicate) :
    state.OccurrenceBoundExtends (state.addRequirements predicates) := by
  exact addRequirementsWithIds state predicates

/-- Marking direct-call provenance preserves the occurrence bound. -/
theorem markDirectCallRequirements (state : State)
    (requirements : List RequirementId) :
    state.OccurrenceBoundExtends
      (state.markDirectCallRequirements requirements) :=
  ⟨Nat.le_refl _, fun below =>
    markDirectCallRequirements_preserves_nodesBelowNextOccurrence
      state requirements below⟩

end OccurrenceBoundExtends

end Solcore.Frontend.SourceInference.State
