import Solcore.Frontend.SourceInference.Types

/-! Allocation and lexical-restoration laws for the typed source state. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.State

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

@[simp] theorem fresh_header (state : State) :
    state.fresh.2.header = state.header := by
  rfl

@[simp] theorem withLocals_header (state : State)
    (locals : TypeSystem.Environment) :
    (state.withLocals locals).header = state.header := by
  rfl

@[simp] theorem restoreLexicalScope_header (state : State)
    (scope : LexicalScope) :
    (state.restoreLexicalScope scope).header = state.header := by
  rfl

@[simp] theorem allocateBinder_header (state : State) (name : String)
    (scheme : TypeSystem.Scheme) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (schemeRequirements : List LocalSchemeRequirement) :
    (state.allocateBinder name scheme span comptime schemeRequirements).2.header =
      state.header := by
  rfl

@[simp] theorem allocateHiddenLocal_header (state : State) :
    state.allocateHiddenLocal.2.header = state.header := by
  rfl

@[simp] theorem allocateExpressionId_header (state : State) :
    state.allocateExpressionId.2.header = state.header := by
  rfl

@[simp] theorem allocateStatementId_header (state : State) :
    state.allocateStatementId.2.header = state.header := by
  rfl

@[simp] theorem recordNode_header (state : State) (node : Node) :
    (state.recordNode node).header = state.header := by
  rfl

@[simp] theorem modifyExpressionNode_header (state : State)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    (state.modifyExpressionNode id modify).header = state.header := by
  rfl

@[simp] theorem modifyStatementNode_header (state : State)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    (state.modifyStatementNode id modify).header = state.header := by
  rfl

@[simp] theorem addRequirementWithId_header (state : State)
    (predicate : ProgramPredicate) :
    (state.addRequirementWithId predicate).2.header = state.header := by
  rfl

@[simp] theorem addRequirementsWithIds_header (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.header = state.header := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simpa [addRequirementsWithIds] using
        induction (state.addRequirementWithId predicate).2

@[simp] theorem markDirectCallRequirements_header (state : State)
    (requirements : List RequirementId) :
    (state.markDirectCallRequirements requirements).header = state.header := by
  rfl

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

@[simp] theorem allocateStatementId_nextOccurrence (state : State) :
    (state.allocateStatementId).2.nextOccurrence =
      state.nextOccurrence + 1 := by
  rfl

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

end Solcore.Frontend.SourceInference.State
