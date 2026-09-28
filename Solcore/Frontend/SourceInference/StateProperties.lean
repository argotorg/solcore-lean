import Solcore.Frontend.SourceInference.Types
import Solcore.TypeSystem.InferenceProperties

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

/-- Every visible stable binder was allocated strictly before the next
declaration-local identity.  Hidden locals advance the same allocator without
appearing in `localBinders`, so this is exactly the bound needed to prove the
next visible binder identity fresh. -/
def LocalBindersBelowNextLocal (state : State) : Prop :=
  ∀ binder ∈ state.localBinders,
    binder.id.binderIndex < state.nextLocal

/-- Every numeric-defaulting origin names a metavariable already allocated by
the inference state.  Finalization needs this allocator bound to invoke the
ordinary unification preservation theorem while closing unresolved numeric
targets. -/
def NumericOriginsBelowNext (state : State) : Prop :=
  (∀ origin ∈ state.integerPatterns,
      origin.metavariable.index < state.inference.next) ∧
    ∀ origin ∈ state.integerLiterals,
      origin.metavariable.index < state.inference.next

/-- The part of source-inference state evolution needed to preserve occurrence
allocation safety.  This deliberately says nothing about exact node payloads:
`attachExpressionCoercions` may refine freshly recorded expression nodes while
still preserving their identities and the allocation bound. -/
structure OccurrenceBoundExtends (before after : State) : Prop where
  nextOccurrence_le : before.nextOccurrence ≤ after.nextOccurrence
  nodesBelowNextOccurrence :
    before.NodesBelowNextOccurrence → after.NodesBelowNextOccurrence

/-- The type-inference portion of a source state has made monotone semantic
progress.  This is intentionally independent of lexical, typed-source, and
requirement-ledger evolution so traversal proofs can compose those invariants
separately. -/
structure InferenceProgress (before after : State) : Prop where
  next_le : before.inference.next ≤ after.inference.next
  solved : after.inference.Solved
  substitution_extends :
    after.inference.substitution.SemanticallyExtends
      before.inference.substitution

/-- A source-inference state is ready for recursive inference when its
substitution is solved and every stable lexical binder lies below the current
type-variable allocator. -/
structure InferenceReady (state : State) : Prop where
  solved : state.inference.Solved
  bindersBelow :
    state.binderEnvironment.BodiesBelow state.inference.next

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

namespace LocalBindersBelowNextLocal

/-- A state update which retains the visible binders and monotonically
advances the shared local allocator preserves the stable-binder bound. -/
theorem transport {before after : State}
    (bindersEq : after.localBinders = before.localBinders)
    (nextLocalLe : before.nextLocal ≤ after.nextLocal)
    (below : before.LocalBindersBelowNextLocal) :
    after.LocalBindersBelowNextLocal := by
  intro binder member
  rw [bindersEq] at member
  exact Nat.lt_of_lt_of_le (below binder member) nextLocalLe

end LocalBindersBelowNextLocal

namespace InferenceProgress

/-- Unchanged inference state is progress whenever its substitution is
already solved. -/
theorem refl {state : State} (solved : state.inference.Solved) :
    state.InferenceProgress state :=
  ⟨Nat.le_refl _, solved,
    TypeSystem.Substitution.SemanticallyExtends.refl_of_solved solved⟩

/-- An unchanged substitution makes allocator growth into semantic inference
progress whenever the input inference state is solved. -/
theorem of_substitution_eq {before after : State}
    (solved : before.inference.Solved)
    (nextLe : before.inference.next ≤ after.inference.next)
    (substitutionEq :
      after.inference.substitution = before.inference.substitution) :
    before.InferenceProgress after := by
  constructor
  · exact nextLe
  · change after.inference.substitution.SolvedBelow after.inference.next
    rw [substitutionEq]
    exact solved.weaken nextLe
  · change after.inference.substitution.SemanticallyExtends
      before.inference.substitution
    rw [substitutionEq]
    exact TypeSystem.Substitution.SemanticallyExtends.refl_of_solved solved

/-- Equality of the inference projections is enough to lift reflexive
progress across a source-state-only update. -/
theorem of_inference_eq {before after : State}
    (solved : before.inference.Solved)
    (inferenceEq : after.inference = before.inference) :
    before.InferenceProgress after := by
  constructor
  · rw [inferenceEq]
    exact Nat.le_refl _
  · rw [inferenceEq]
    exact solved
  · rw [inferenceEq]
    exact TypeSystem.Substitution.SemanticallyExtends.refl_of_solved solved

/-- Inference progress composes across sequential source traversals. -/
theorem trans {first second third : State}
    (firstSecond : first.InferenceProgress second)
    (secondThird : second.InferenceProgress third) :
    first.InferenceProgress third :=
  ⟨Nat.le_trans firstSecond.next_le secondThird.next_le,
    secondThird.solved,
    TypeSystem.Substitution.SemanticallyExtends.trans
      secondThird.substitution_extends firstSecond.substitution_extends⟩

/-- Resolving a type that was bounded before semantic inference progress
produces a type bounded by the advanced allocator. -/
theorem resolve_variablesBelow {before after : State}
    (progress : before.InferenceProgress after) {type : TypeSystem.Ty}
    (below : type.VariablesBelow before.inference.next) :
    (after.resolve type).VariablesBelow after.inference.next := by
  exact progress.solved.variablesBelow_apply
    (below.weaken progress.next_le)

end InferenceProgress

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

/-- Initial source inference has no numeric origins, so its origin allocator
bound holds independently of the input environment. -/
theorem initial_numericOriginsBelowNext
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (inputComptime : List Bool) :
    (initial owner locals inputComptime).NumericOriginsBelowNext := by
  constructor <;> simp [initial]

/-- Stable input binders reconstruct the complete initial inference
environment, including schemes and source order. -/
@[simp] theorem initial_binderEnvironment
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (inputComptime : List Bool) :
    (initial owner locals inputComptime).binderEnvironment = locals := by
  rw [binderEnvironment, ← initial_inputs_eq_localBinders,
    initial_inputs_definition, map_mapIdx]
  induction locals with
  | nil => rfl
  | cons entry rest induction =>
      simp [List.mapIdx_cons, induction]

private theorem lookupBinder?_eq_some_raw_and_templates
    {state : State} {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    state.localBinders.find? (fun candidate => candidate.name == name) =
        some binder ∧
      binder.schemeRequirements.map
          (fun requirement => requirement.templateRequirement) ⊆
        state.localSchemeAssumptions := by
  unfold lookupBinder? at found
  cases rawFound : state.localBinders.find?
      (fun candidate => candidate.name == name) with
  | none => simp [rawFound] at found
  | some candidate =>
      simp only [rawFound] at found
      split at found
      next guarded =>
        injection found with candidateEq
        subst candidate
        exact ⟨rfl, guarded⟩
      next => contradiction

/-- Guarded lookup retains the ordinary first-match result selected before the
template-classification check. -/
theorem lookupBinder?_eq_some_raw
    {state : State} {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    state.localBinders.find? (fun candidate => candidate.name == name) =
      some binder :=
  (lookupBinder?_eq_some_raw_and_templates found).1

/-- Successful lexical lookup returns a retained stable binder whose source
name is exactly the queried name. -/
theorem lookupBinder?_eq_some_facts
    {state : State} {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    binder ∈ state.localBinders ∧ binder.name = name := by
  have rawFound := lookupBinder?_eq_some_raw found
  have accepted : (binder.name == name) = true :=
    List.find?_some
      (p := fun candidate : TypedBinder => candidate.name == name) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound, by simpa using accepted⟩

/-- A successfully looked-up binder exposes only requirement templates already
classified as local-scheme assumptions.  This is guaranteed at the lookup
boundary even for an otherwise malformed inference state. -/
theorem lookupBinder?_eq_some_templates_subset
    {state : State} {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    binder.schemeRequirements.map
        (fun requirement => requirement.templateRequirement) ⊆
      state.localSchemeAssumptions :=
  (lookupBinder?_eq_some_raw_and_templates found).2

/-- Successful lexical lookup exposes the selected scheme under the queried
name in the canonical binder environment. -/
theorem lookupBinder?_eq_some_mem_binderEnvironment
    {state : State} {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    (name, binder.scheme) ∈ state.binderEnvironment := by
  rcases lookupBinder?_eq_some_facts found with
    ⟨binderMember, nameEq⟩
  apply List.mem_map.mpr
  exact ⟨binder, binderMember, by simp [nameEq]⟩

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

/-- Initial parameter binders occupy exactly the indices below the initial
local allocator. -/
theorem initial_localBindersBelowNextLocal
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (inputComptime : List Bool) :
    (initial owner locals inputComptime).LocalBindersBelowNextLocal := by
  intro binder member
  change binder.id.binderIndex < locals.length
  rw [← initial_inputs_eq_localBinders] at member
  rw [initial_inputs_definition] at member
  obtain ⟨index, indexLt, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  exact indexLt

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

/-- Compatibility-environment replacement cannot affect the stable binder
environment used by local generalization. -/
@[simp] theorem withLocals_binderEnvironment (state : State)
    (locals : TypeSystem.Environment) :
    (state.withLocals locals).binderEnvironment = state.binderEnvironment := by
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

/-- Restoring a captured lexical scope makes that scope observable again. -/
@[simp] theorem restoreLexicalScope_lexicalScope (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).lexicalScope = scope := by
  cases scope
  rfl

/-- Restoring a lexical scope reconstructs its binder environment, regardless
of the compatibility environment carried by the current inner state. -/
@[simp] theorem restoreLexicalScope_binderEnvironment (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).binderEnvironment =
      scope.binders.map fun binder => (binder.name, binder.scheme) := by
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

/-- Visible allocation extends the stable binder environment at its
first-match head. -/
@[simp] theorem allocateBinder_binderEnvironment
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement) :
    (state.allocateBinder name scheme span comptime
      schemeRequirements).2.binderEnvironment =
      (name, scheme) :: state.binderEnvironment := by
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

/-! Stable-local allocator preservation.  These lemmas mirror the primitive
state updates used by recursive inference without coupling the local identity
invariant to type-inference or requirement-ledger invariants. -/

/-- Fresh type-variable allocation leaves stable locals unchanged. -/
theorem fresh_preserves_localBindersBelowNextLocal
    (state : State) (below : state.LocalBindersBelowNextLocal) :
    state.fresh.2.LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Replacing the compatibility name environment leaves stable locals
unchanged. -/
theorem withLocals_preserves_localBindersBelowNextLocal
    (state : State) (locals : TypeSystem.Environment)
    (below : state.LocalBindersBelowNextLocal) :
    (state.withLocals locals).LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Restoring a captured outer scope preserves its binder bound when the
inner traversal has only advanced the declaration-wide local allocator. -/
theorem restoreLexicalScope_preserves_localBindersBelowNextLocal
    {outer inner : State}
    (below : outer.LocalBindersBelowNextLocal)
    (nextLocalLe : outer.nextLocal ≤ inner.nextLocal) :
    (inner.restoreLexicalScope outer.lexicalScope)
      |>.LocalBindersBelowNextLocal := by
  intro binder member
  change binder ∈ outer.localBinders at member
  change binder.id.binderIndex < inner.nextLocal
  exact Nat.lt_of_lt_of_le (below binder member) nextLocalLe

/-- Visible binder allocation preserves the bound by placing the new binder at
the old cutoff and advancing that cutoff once. -/
theorem allocateBinder_preserves_localBindersBelowNextLocal
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement)
    (below : state.LocalBindersBelowNextLocal) :
    (state.allocateBinder name scheme span comptime schemeRequirements).2
      |>.LocalBindersBelowNextLocal := by
  intro binder member
  simp only [allocateBinder, List.mem_cons] at member
  change binder.id.binderIndex < state.nextLocal + 1
  rcases member with rfl | member
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (below binder member)

/-- The binder returned by visible allocation is fresh for the entire retained
stable-binder stack. -/
theorem allocateBinder_id_fresh
    (state : State) (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (schemeRequirements : List LocalSchemeRequirement)
    (below : state.LocalBindersBelowNextLocal) :
    (state.allocateBinder name scheme span comptime schemeRequirements).1.id ∉
      state.localBinders.map fun binder => binder.id := by
  intro member
  rcases List.mem_map.mp member with
    ⟨retained, retainedMember, idEq⟩
  have indexEq := congrArg
    (fun id : Resolved.LocalId => id.binderIndex) idEq
  have retainedBelow := below retained retainedMember
  exact (Nat.ne_of_lt retainedBelow) (by
    simpa [allocateBinder] using indexEq)

/-- The freshness result can be consumed directly from the usual successful
allocation equation used by traversal proofs. -/
theorem allocateBinder_success_id_fresh
    {state final : State} {name : String} {scheme : TypeSystem.Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement}
    {binder : TypedBinder}
    (below : state.LocalBindersBelowNextLocal)
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final)) :
    binder.id ∉ state.localBinders.map fun retained => retained.id := by
  have binderEq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 = binder :=
    congrArg Prod.fst allocated
  subst binder
  exact allocateBinder_id_fresh state name scheme span comptime
    schemeRequirements below

/-- Hidden-local reservation advances the shared cutoff, so all visible
binders remain below it. -/
theorem allocateHiddenLocal_preserves_localBindersBelowNextLocal
    (state : State) (below : state.LocalBindersBelowNextLocal) :
    state.allocateHiddenLocal.2.LocalBindersBelowNextLocal := by
  intro binder member
  change binder.id.binderIndex < state.nextLocal + 1
  exact Nat.lt_succ_of_lt (below binder member)

/-- The hidden identity reserved at the current cutoff is also fresh for the
visible stable-binder stack. -/
theorem allocateHiddenLocal_id_fresh
    (state : State) (below : state.LocalBindersBelowNextLocal) :
    state.allocateHiddenLocal.1 ∉
      state.localBinders.map fun binder => binder.id := by
  intro member
  rcases List.mem_map.mp member with
    ⟨retained, retainedMember, idEq⟩
  have indexEq := congrArg
    (fun id : Resolved.LocalId => id.binderIndex) idEq
  exact (Nat.ne_of_lt (below retained retainedMember)) (by
    simpa [allocateHiddenLocal] using indexEq)

/-- Expression identity allocation leaves the local allocator unchanged. -/
theorem allocateExpressionId_preserves_localBindersBelowNextLocal
    (state : State) (below : state.LocalBindersBelowNextLocal) :
    state.allocateExpressionId.2.LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Statement identity allocation leaves the local allocator unchanged. -/
theorem allocateStatementId_preserves_localBindersBelowNextLocal
    (state : State) (below : state.LocalBindersBelowNextLocal) :
    state.allocateStatementId.2.LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Recording a node leaves the local allocator unchanged. -/
theorem recordNode_preserves_localBindersBelowNextLocal
    (state : State) (node : Node)
    (below : state.LocalBindersBelowNextLocal) :
    (state.recordNode node).LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Refining an expression node leaves the local allocator unchanged. -/
theorem modifyExpressionNode_preserves_localBindersBelowNextLocal
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (below : state.LocalBindersBelowNextLocal) :
    (state.modifyExpressionNode id modify).LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Refining a statement node leaves the local allocator unchanged. -/
theorem modifyStatementNode_preserves_localBindersBelowNextLocal
    (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (below : state.LocalBindersBelowNextLocal) :
    (state.modifyStatementNode id modify).LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Allocating one requirement leaves the local allocator unchanged. -/
theorem addRequirementWithId_preserves_localBindersBelowNextLocal
    (state : State) (predicate : ProgramPredicate)
    (below : state.LocalBindersBelowNextLocal) :
    (state.addRequirementWithId predicate).2.LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
  exact below

/-- Adding one requirement leaves the local allocator unchanged. -/
theorem addRequirement_preserves_localBindersBelowNextLocal
    (state : State) (predicate : ProgramPredicate)
    (below : state.LocalBindersBelowNextLocal) :
    (state.addRequirement predicate).LocalBindersBelowNextLocal := by
  exact addRequirementWithId_preserves_localBindersBelowNextLocal
    state predicate below

/-- Allocating a requirement row leaves the local allocator unchanged. -/
theorem addRequirementsWithIds_preserves_localBindersBelowNextLocal
    (state : State) (predicates : List ProgramPredicate)
    (below : state.LocalBindersBelowNextLocal) :
    (state.addRequirementsWithIds predicates).2
      |>.LocalBindersBelowNextLocal := by
  induction predicates generalizing state with
  | nil => simpa [addRequirementsWithIds] using below
  | cons predicate rest induction =>
      simp only [addRequirementsWithIds]
      exact induction (state.addRequirementWithId predicate).2
        (addRequirementWithId_preserves_localBindersBelowNextLocal
          state predicate below)

/-- Adding requirements leaves the local allocator unchanged. -/
theorem addRequirements_preserves_localBindersBelowNextLocal
    (state : State) (predicates : List ProgramPredicate)
    (below : state.LocalBindersBelowNextLocal) :
    (state.addRequirements predicates).LocalBindersBelowNextLocal := by
  exact addRequirementsWithIds_preserves_localBindersBelowNextLocal
    state predicates below

/-- Direct-call provenance metadata leaves the local allocator unchanged. -/
theorem markDirectCallRequirements_preserves_localBindersBelowNextLocal
    (state : State) (requirements : List RequirementId)
    (below : state.LocalBindersBelowNextLocal) :
    (state.markDirectCallRequirements requirements)
      |>.LocalBindersBelowNextLocal := by
  change state.LocalBindersBelowNextLocal
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

namespace InferenceProgress

/-- Allocating a fresh type metavariable advances the inference allocator,
preserves solvedness, and leaves the existing substitution meaning intact. -/
theorem fresh (state : State) (solved : state.inference.Solved) :
    state.InferenceProgress state.fresh.2 := by
  constructor
  · change state.inference.next ≤ state.inference.next + 1
    exact Nat.le_succ _
  · change state.inference.fresh.2.Solved
    exact TypeSystem.InferState.Solved.fresh solved
  · change state.inference.substitution.SemanticallyExtends
      state.inference.substitution
    exact TypeSystem.Substitution.SemanticallyExtends.refl_of_solved solved

/-- Replacing compatibility locals leaves type inference unchanged. -/
theorem withLocals (state : State) (locals : TypeSystem.Environment)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.withLocals locals) :=
  of_inference_eq solved rfl

/-- Restoring lexical scope leaves type inference unchanged. -/
theorem restoreLexicalScope (state : State) (scope : LexicalScope)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.restoreLexicalScope scope) :=
  of_inference_eq solved rfl

/-- Stable-binder allocation leaves type inference unchanged. -/
theorem allocateBinder (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (schemeRequirements : List LocalSchemeRequirement)
    (solved : state.inference.Solved) :
    state.InferenceProgress
      (state.allocateBinder name scheme span comptime schemeRequirements).2 :=
  of_inference_eq solved rfl

/-- Hidden-local allocation leaves type inference unchanged. -/
theorem allocateHiddenLocal (state : State)
    (solved : state.inference.Solved) :
    state.InferenceProgress state.allocateHiddenLocal.2 :=
  of_inference_eq solved rfl

/-- Expression-identity allocation leaves type inference unchanged. -/
theorem allocateExpressionId (state : State)
    (solved : state.inference.Solved) :
    state.InferenceProgress state.allocateExpressionId.2 :=
  of_inference_eq solved rfl

/-- Statement-identity allocation leaves type inference unchanged. -/
theorem allocateStatementId (state : State)
    (solved : state.inference.Solved) :
    state.InferenceProgress state.allocateStatementId.2 :=
  of_inference_eq solved rfl

/-- Recording a typed-source node leaves type inference unchanged. -/
theorem recordNode (state : State) (node : Node)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.recordNode node) :=
  of_inference_eq solved rfl

/-- Refining an expression node leaves type inference unchanged. -/
theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.modifyExpressionNode id modify) :=
  of_inference_eq solved rfl

/-- Refining a statement node leaves type inference unchanged. -/
theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.modifyStatementNode id modify) :=
  of_inference_eq solved rfl

/-- Allocating one requirement leaves type inference unchanged. -/
theorem addRequirementWithId (state : State)
    (predicate : ProgramPredicate) (solved : state.inference.Solved) :
    state.InferenceProgress (state.addRequirementWithId predicate).2 :=
  of_inference_eq solved rfl

/-- Adding one requirement leaves type inference unchanged. -/
theorem addRequirement (state : State) (predicate : ProgramPredicate)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.addRequirement predicate) :=
  of_inference_eq solved rfl

/-- Allocating a list of requirements leaves type inference unchanged. -/
theorem addRequirementsWithIds (state : State)
    (predicates : List ProgramPredicate) (solved : state.inference.Solved) :
    state.InferenceProgress (state.addRequirementsWithIds predicates).2 := by
  induction predicates generalizing state with
  | nil => exact .refl solved
  | cons predicate rest induction =>
      simpa only [State.addRequirementsWithIds] using
        (addRequirementWithId state predicate solved).trans
          (induction (state.addRequirementWithId predicate).2
            (addRequirementWithId state predicate solved).solved)

/-- Adding a list of requirements leaves type inference unchanged. -/
theorem addRequirements (state : State) (predicates : List ProgramPredicate)
    (solved : state.inference.Solved) :
    state.InferenceProgress (state.addRequirements predicates) :=
  addRequirementsWithIds state predicates solved

/-- Marking direct-call provenance leaves type inference unchanged. -/
theorem markDirectCallRequirements (state : State)
    (requirements : List RequirementId) (solved : state.inference.Solved) :
    state.InferenceProgress
      (state.markDirectCallRequirements requirements) :=
  of_inference_eq solved rfl

end InferenceProgress

namespace InferenceReady

/-- Semantic inference progress preserves readiness when the stable lexical
binder environment is unchanged. -/
theorem of_progress_of_binderEnvironment_eq {before after : State}
    (ready : before.InferenceReady)
    (progress : before.InferenceProgress after)
    (binderEnvironmentEq :
      after.binderEnvironment = before.binderEnvironment) :
    after.InferenceReady := by
  constructor
  · exact progress.solved
  · rw [binderEnvironmentEq]
    exact ready.bindersBelow.weaken progress.next_le

/-- A successfully looked-up binder in a ready state has a scheme body below
the state's current flexible-variable allocator. -/
theorem lookupBinder?_body_variablesBelow
    {state : State} (ready : state.InferenceReady)
    {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    binder.scheme.body.VariablesBelow state.inference.next := by
  exact ready.bindersBelow (name, binder.scheme)
    (lookupBinder?_eq_some_mem_binderEnvironment found)

/-- Consequently, every unquantified free variable of a successfully
looked-up binder scheme lies below the current allocator. -/
theorem lookupBinder?_freeVariablesBelow
    {state : State} (ready : state.InferenceReady)
    {name : String} {binder : TypedBinder}
    (found : state.lookupBinder? name = some binder) :
    binder.scheme.FreeVariablesBelow state.inference.next := by
  exact TypeSystem.Scheme.FreeVariablesBelow.of_body
    (lookupBinder?_body_variablesBelow ready found)

/-- Initial inference is solved and starts at the exact allocator bound
computed from its input environment. -/
theorem initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment) (inputComptime : List Bool) :
    (State.initial owner locals inputComptime).InferenceReady := by
  constructor
  · change (TypeSystem.InferState.initial locals.nextVariable).Solved
    exact TypeSystem.InferState.Solved.initial locals.nextVariable
  · rw [initial_binderEnvironment]
    change locals.BodiesBelow locals.nextVariable
    exact TypeSystem.Environment.bodiesBelow_nextVariable locals

/-- Fresh type-variable allocation preserves readiness by weakening all
existing binder bounds to the advanced allocator. -/
theorem fresh {state : State} (ready : state.InferenceReady) :
    state.fresh.2.InferenceReady := by
  constructor
  · change state.inference.fresh.2.Solved
    exact TypeSystem.InferState.Solved.fresh ready.solved
  · change state.binderEnvironment.BodiesBelow (state.inference.next + 1)
    exact ready.bindersBelow.weaken (Nat.le_succ _)

/-- Replacing the compatibility-only local cache preserves readiness. -/
theorem withLocals {state : State} (locals : TypeSystem.Environment)
    (ready : state.InferenceReady) :
    (state.withLocals locals).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Restoring a lexical scope is ready when the restored stable binders are
explicitly known to lie below the unchanged inference allocator. -/
theorem restoreLexicalScope {state : State} (scope : LexicalScope)
    (ready : state.InferenceReady)
    (scopeBelow :
      TypeSystem.Environment.BodiesBelow state.inference.next
        (scope.binders.map fun binder => (binder.name, binder.scheme))) :
    (state.restoreLexicalScope scope).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change TypeSystem.Environment.BodiesBelow state.inference.next
      (scope.binders.map fun binder => (binder.name, binder.scheme))
    exact scopeBelow

/-- Entering one stable binder preserves readiness when its scheme body is
bounded by the current allocator. -/
theorem allocateBinder {state : State} (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (schemeRequirements : List LocalSchemeRequirement)
    (ready : state.InferenceReady)
    (bodyBelow : scheme.body.VariablesBelow state.inference.next) :
    (state.allocateBinder name scheme span comptime
      schemeRequirements).2.InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · rw [allocateBinder_binderEnvironment]
    exact TypeSystem.Environment.BodiesBelow.cons
      bodyBelow ready.bindersBelow

/-- Hidden-local allocation does not change inference readiness. -/
theorem allocateHiddenLocal {state : State} (ready : state.InferenceReady) :
    state.allocateHiddenLocal.2.InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Expression-identity allocation does not change inference readiness. -/
theorem allocateExpressionId {state : State} (ready : state.InferenceReady) :
    state.allocateExpressionId.2.InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Statement-identity allocation does not change inference readiness. -/
theorem allocateStatementId {state : State} (ready : state.InferenceReady) :
    state.allocateStatementId.2.InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Recording a typed-source node does not change inference readiness. -/
theorem recordNode {state : State} (node : Node)
    (ready : state.InferenceReady) :
    (state.recordNode node).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Refining an expression node does not change inference readiness. -/
theorem modifyExpressionNode {state : State} (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) (ready : state.InferenceReady) :
    (state.modifyExpressionNode id modify).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Refining a statement node does not change inference readiness. -/
theorem modifyStatementNode {state : State} (id : StatementId)
    (modify : StatementNode → StatementNode) (ready : state.InferenceReady) :
    (state.modifyStatementNode id modify).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Allocating one requirement does not change inference readiness. -/
theorem addRequirementWithId {state : State} (predicate : ProgramPredicate)
    (ready : state.InferenceReady) :
    (state.addRequirementWithId predicate).2.InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Adding one requirement does not change inference readiness. -/
theorem addRequirement {state : State} (predicate : ProgramPredicate)
    (ready : state.InferenceReady) :
    (state.addRequirement predicate).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

/-- Allocating a list of requirements does not change inference readiness. -/
theorem addRequirementsWithIds {state : State}
    (predicates : List ProgramPredicate) (ready : state.InferenceReady) :
    (state.addRequirementsWithIds predicates).2.InferenceReady := by
  induction predicates generalizing state with
  | nil => exact ready
  | cons predicate rest induction =>
      simpa only [State.addRequirementsWithIds] using
        induction
          (addRequirementWithId predicate ready)

/-- Adding a list of requirements does not change inference readiness. -/
theorem addRequirements {state : State} (predicates : List ProgramPredicate)
    (ready : state.InferenceReady) :
    (state.addRequirements predicates).InferenceReady :=
  addRequirementsWithIds predicates ready

/-- Recording direct-call requirement provenance does not change inference
readiness. -/
theorem markDirectCallRequirements {state : State}
    (requirements : List RequirementId) (ready : state.InferenceReady) :
    (state.markDirectCallRequirements requirements).InferenceReady := by
  constructor
  · change state.inference.Solved
    exact ready.solved
  · change state.binderEnvironment.BodiesBelow state.inference.next
    exact ready.bindersBelow

end InferenceReady

/-- Restoring the outer lexical scope after inner inference preserves the
inner inference result while re-establishing readiness from the outer binder
bound.  No readiness premise is needed for the un-restored inner state. -/
theorem restoreLexicalScope_inferenceProperties
    {outer inner : State}
    (ready : outer.InferenceReady)
    (progress : outer.InferenceProgress inner) :
    outer.InferenceProgress
        (inner.restoreLexicalScope outer.lexicalScope) ∧
      (inner.restoreLexicalScope outer.lexicalScope).InferenceReady := by
  have restoreProgress :
      inner.InferenceProgress
        (inner.restoreLexicalScope outer.lexicalScope) :=
    InferenceProgress.restoreLexicalScope inner outer.lexicalScope
      progress.solved
  refine ⟨progress.trans restoreProgress, ?_⟩
  constructor
  · change inner.inference.Solved
    exact progress.solved
  · change outer.binderEnvironment.BodiesBelow inner.inference.next
    exact ready.bindersBelow.weaken progress.next_le

end Solcore.Frontend.SourceInference.State
