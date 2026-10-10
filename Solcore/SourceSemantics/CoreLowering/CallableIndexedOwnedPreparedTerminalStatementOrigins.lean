import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-! The actual contextual compiler may read a type-substituted statement table.
These receipts recover the same original terminal occurrence and its preserved
form. They do not identify the original and substituted statement types. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalStatementOrigins
open Core Frontend SourceInference
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)

/-- A substituted statement member retains its exact original occurrence.
The original node and its substituted node remain separate. -/
theorem substituted_contains {original : TypedSource} {active : TypeSystem.Substitution}
    {id : StatementId} {node : StatementNode}
    (contains : SourceSemantics.ContainsStatement (original.applySubstitution active) id node) :
    ∃ before, SourceSemantics.ContainsStatement original id before ∧
      node = before.applySubstitution active := by
  obtain ⟨retained, member, same⟩ := List.mem_map.mp contains.1
  cases retained with
  | expression before => cases same
  | statement before =>
    cases same
    exact ⟨before, ⟨member, contains.2⟩, rfl⟩

theorem substituted_returning_iff (active : TypeSystem.Substitution) (node : StatementNode)
    (expression : ExpressionId) :
    (node.applySubstitution active).form = .returnStmt (some expression) ↔
      node.form = .returnStmt (some expression) := by
  cases form : node.form <;>
    simp [StatementNode.applySubstitution, StatementForm.applySubstitution, form]

theorem substituted_tail_iff (active : TypeSystem.Substitution) (node : StatementNode)
    (expression : ExpressionId) :
    (node.applySubstitution active).form = .expression expression false ↔
      node.form = .expression expression false := by
  cases form : node.form <;>
    simp [StatementNode.applySubstitution, StatementForm.applySubstitution, form]

/-- The actual accepted compiler node selects the original return occurrence. -/
theorem returning_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    (contains : SourceSemantics.ContainsStatement actual id node)
    (form : node.form = .returnStmt (some expression)) :
    ∃ before, SourceSemantics.ContainsStatement original id before ∧
      before.form = .returnStmt (some expression) := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_returning_iff active before expression).mp form⟩

theorem tail_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    (contains : SourceSemantics.ContainsStatement actual id node)
    (form : node.form = .expression expression false) :
    ∃ before, SourceSemantics.ContainsStatement original id before ∧
      before.form = .expression expression false := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_tail_iff active before expression).mp form⟩

/-- A real compiler lookup and source view construct the original staged Head. -/
theorem returning_head {invocation : Staging.Recursive.Scope} {actual : TypedSource}
    (view : SourceView invocation.source actual) {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} (rest : List StatementId)
    (found : actual.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression)) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression (id :: rest) := by
  obtain ⟨before, retained, beforeForm⟩ := returning_origin view (lookupStatement?_sound found) form
  exact .returning rest retained beforeForm

theorem tail_head {invocation : Staging.Recursive.Scope} {actual : TypedSource}
    (view : SourceView invocation.source actual) {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} (found : actual.lookupStatement? id = some node)
    (form : node.form = .expression expression false) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression [id] := by
  obtain ⟨before, retained, beforeForm⟩ := tail_origin view (lookupStatement?_sound found) form
  exact .tail retained beforeForm

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalStatementOrigins
