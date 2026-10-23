import Solcore.Frontend.ResidualScopeTails
import Solcore.Frontend.ResidualLexicalScopes
import Solcore.SourceSemantics.SourceSpecializationStatementReferences
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability

/-! Canonical source-reference paths extend the validator's actual residual
scope. The suffix keeps its starting scope, so variables introduced by nested
declarations can be distinguished from variables captured at body entry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open CallableLambdaBodyReachability

private theorem expression_node {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

private theorem statement_node {source : TypedSource} {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) :
    source.lookupNode? id.occurrence = some (.statement node) := by
  unfold TypedSource.lookupStatement? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | expression => simp [selected] at found
    | statement statement =>
      have same : statement = node := by simpa [selected] using found
      simp only [same]

private theorem scheduled_expression {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) (variables : List TypeVarId) :
    ∃ next, (child, next) ∈ residualScopeChildren source (.expression id) variables := by
  have selected : child ∈
      (residualScopeChildren source (.expression id) variables).map Prod.fst := by
    rw [residualScopeChildren_ids]
    simpa only [NodeId.occurrenceId, expression_node found,
      expressionChildNodeIds_eq_references] using edge
  obtain ⟨pair, member, same⟩ := List.mem_map.mp selected
  exact ⟨pair.2, same ▸ member⟩

private theorem scheduled_statement {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) (variables : List TypeVarId) :
    ∃ next, (child, next) ∈ residualScopeChildren source (.statement id) variables := by
  have selected : child ∈
      (residualScopeChildren source (.statement id) variables).map Prod.fst := by
    rw [residualScopeChildren_ids]
    simpa only [NodeId.occurrenceId, statement_node found] using
      statementChildNodeIds_of_reference (source := source) edge
  obtain ⟨pair, member, same⟩ := List.mem_map.mp selected
  exact ⟨pair.2, same ▸ member⟩

/-- Every real reference path from this root extends the same starting scope;
neither a global node-coverage law nor a different path is used. -/
theorem tail_of_reaches {source : TypedSource} {root node : NodeId}
    (path : Reaches source [root] node) (variables : List TypeVarId) :
    ∃ next, ResidualScopeTail source root variables node next := by
  induction path with
  | root member =>
    cases List.mem_singleton.mp member
    exact ⟨variables, .refl⟩
  | expression _ found edge ih =>
    obtain ⟨before, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_expression found edge before
    exact ⟨next, .child tail scheduled⟩
  | statement _ found edge ih =>
    obtain ⟨before, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_statement found edge before
    exact ⟨next, .child tail scheduled⟩

/-- Body execution selects one actual root. The returned evidence preserves
that root's covered entry scope and every later scheduled edge. -/
theorem covered_root_of_reaches {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {node : NodeId} (path : Reaches source roots node) :
    ∃ root firstVariables variables,
      root ∈ roots ∧ ResidualScopePath source root firstVariables ∧
      firstVariables ⊆ domain ∧ ResidualScopeTail source root firstVariables node variables := by
  induction path with
  | @root id member =>
    obtain ⟨variables, scope, supported⟩ := covered id member
    exact ⟨id, variables, variables, member, scope, supported, .refl⟩
  | expression _ found edge ih =>
    obtain ⟨root, firstVariables, variables, member, scope, supported, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_expression found edge variables
    exact ⟨root, firstVariables, next, member, scope, supported, .child tail scheduled⟩
  | statement _ found edge ih =>
    obtain ⟨root, firstVariables, variables, member, scope, supported, tail⟩ := ih
    obtain ⟨next, scheduled⟩ := scheduled_statement found edge variables
    exact ⟨root, firstVariables, next, member, scope, supported, .child tail scheduled⟩

/-- Variables outside the covered entry were introduced by an initialized
statement on this same canonical body path. The complete statement lookup is
retained for the actual allocation-order producer. -/
theorem scope_of_reaches {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {node : NodeId} (path : Reaches source roots node) :
    ∃ variables, ResidualScopePath source node variables ∧
      ∀ metavariable ∈ variables, metavariable ∈ domain ∨
        ∃ id statement binder initializer,
          Reaches source roots (.statement id) ∧
          source.lookupStatement? id = some statement ∧
          statement.form = .letDecl binder (some initializer) ∧
          metavariable ∈ binder.scheme.quantified := by
  induction path with
  | @root id member =>
    obtain ⟨variables, scope, supported⟩ := covered id member
    exact ⟨variables, scope, fun _ occurs => .inl (supported occurs)⟩
  | @expression id node child parent found edge ih =>
    obtain ⟨before, scope, origins⟩ := ih
    obtain ⟨variables, scheduled⟩ := scheduled_expression found edge before
    refine ⟨variables, .child scope scheduled, ?_⟩
    intro metavariable present
    by_cases old : metavariable ∈ before
    · exact origins metavariable old
    · obtain ⟨statement, binder, initializer, impossible, _, _, _⟩ :=
        residualScopeChildren_new_quantifier scheduled present old
      simp only [NodeId.occurrenceId, expression_node found] at impossible
      cases impossible
  | @statement id node child parent found edge ih =>
    obtain ⟨before, scope, origins⟩ := ih
    obtain ⟨variables, scheduled⟩ := scheduled_statement found edge before
    refine ⟨variables, .child scope scheduled, ?_⟩
    intro metavariable present
    by_cases old : metavariable ∈ before
    · exact origins metavariable old
    · obtain ⟨statement, binder, initializer, selected, form, _, owned⟩ :=
        residualScopeChildren_new_quantifier scheduled present old
      have same : statement = node :=
        Node.statement.inj (Option.some.inj (selected.symm.trans (statement_node found)))
      subst statement
      exact .inr ⟨id, node, binder, initializer, parent, found, form, owned⟩

/-- A real initialized loop item is scheduled from the retained loop
statement. That scheduler preserves its inherited residual scope. -/
theorem capture_header {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {id : StatementId} (path : LocalLambdaLexicalPath source roots (.statement id))
    {statement : StatementNode} (found : source.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ initializers ++ post) :
    CapturedResidualScope source initializer binder.scheme.quantified domain := by
  obtain ⟨before, scope, inherited⟩ := path.statement_scope covered
  have present : NodeId.expression initializer ∈
      (initializers ++ post).flatMap ForItemForm.references :=
    List.mem_flatMap.mpr ⟨.letDecl binder (some initializer), member,
      by simp [ForItemForm.references]⟩
  have edge : NodeId.expression initializer ∈ statement.form.references := by
    simp only [List.flatMap_append, List.mem_append] at present
    simp only [form, StatementForm.references, List.mem_append]
    exact present.elim (fun p => .inl (.inl (.inl p))) (fun p => .inl (.inr p))
  obtain ⟨variables, scheduled⟩ := scheduled_statement found edge before
  refine ⟨variables, .child scope scheduled, ?_⟩
  intro metavariable occurs
  by_cases old : metavariable ∈ before
  · exact .inr (inherited old)
  · obtain ⟨other, owner, initialized, selected, initializedForm, _, _⟩ :=
      residualScopeChildren_new_quantifier scheduled occurs old
    have same : other = statement :=
      Node.statement.inj (Option.some.inj (selected.symm.trans (statement_node found)))
    subst other
    rw [form] at initializedForm
    cases initializedForm

end Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
