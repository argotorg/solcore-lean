import Solcore.Frontend.SourceInference.Types

/-! Allocation and lexical-restoration laws for the typed source state. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.State

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
