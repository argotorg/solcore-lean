import Solcore.Frontend.SourceSpecializationWorklist

/-! A direct lexical execution keeps its entry scope until it reaches an
actual generalized-lambda initializer. That initializer is a traversal leaf,
and its newly added scope is precisely owned by the enclosing let. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem SourceSpecialization

/-- The boundary includes the genuine source let and the exact initializer.
The variables inherited from the invocation remain separate from this owner. -/
def LexicalScopeBoundary (source : TypedSource) (entry : List TypeVarId)
    (node : NodeId) (variables : List TypeVarId) : Prop :=
  ∃ (parent : NodeId) (statement : StatementNode) (binder : TypedBinder) (initializer : ExpressionId),
    source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
    statement.form = .letDecl binder (some initializer) ∧
    node = .expression initializer ∧
    isDirectLambdaInitializer source initializer = true ∧
    (∀ metavariable ∈ variables,
      metavariable ∈ entry ∨ metavariable ∈ binder.scheme.quantified) ∧
    localLambdaLexicalChildren source node = []

/-- Both alternatives refer to the same actual residual path. The second is
only the initializer leaf, never an arbitrary later body node. -/
theorem LocalLambdaLexicalPath.scope {source : TypedSource} {roots : List NodeId}
    {node : NodeId} (path : LocalLambdaLexicalPath source roots node)
    {entry : List TypeVarId}
    (initial : ∀ root ∈ roots, ∃ variables, ResidualScopePath source root variables ∧
      variables ⊆ entry) :
    ∃ variables, ResidualScopePath source node variables ∧
      (variables ⊆ entry ∨ LexicalScopeBoundary source entry node variables) := by
  classical
  induction path with
  | root member =>
    obtain ⟨variables, scope, supported⟩ := initial _ member
    exact ⟨variables, scope, .inl supported⟩
  | @child parent node prior edge ih =>
    obtain ⟨before, scope, contained | boundary⟩ := ih
    · obtain ⟨variables, scheduled⟩ := localLambdaLexicalChildren_residual edge before
      refine ⟨variables, .child scope scheduled, ?_⟩
      by_cases inherited : variables ⊆ entry
      · exact .inl inherited
      · have witness : ∃ metavariable, metavariable ∈ variables ∧ metavariable ∉ entry := by
          apply Classical.byContradiction
          intro absent
          apply inherited
          intro candidate member
          apply Classical.byContradiction
          intro fresh
          exact absent ⟨candidate, member, fresh⟩
        obtain ⟨metavariable, occurs, fresh⟩ := witness
        have outside : metavariable ∉ before := fun member => fresh (contained member)
        obtain ⟨statement, binder, initializer, found, form, same, _, direct⟩ :=
          residualScopeChildren_new_quantifier_direct scheduled occurs outside
        apply Or.inr
        refine ⟨parent, statement, binder, initializer, found, form, same, direct, ?_,
          localLambdaLexicalChildren_scope_boundary scheduled occurs outside⟩
        intro candidate present
        by_cases inherited : candidate ∈ entry
        · exact .inl inherited
        · have outside : candidate ∉ before := fun member => inherited (contained member)
          obtain ⟨otherStatement, otherBinder, otherInitializer, otherFound, otherForm,
            _, owned⟩ := residualScopeChildren_new_quantifier scheduled present outside
          have sameStatement : otherStatement = statement :=
            Node.statement.inj (Option.some.inj (otherFound.symm.trans found))
          subst otherStatement
          have sameBinder : otherBinder = binder :=
            (StatementForm.letDecl.inj (otherForm.symm.trans form)).1
          exact .inr (sameBinder ▸ owned)
    · obtain ⟨_, _, _, _, _, _, _, _, _, stopped⟩ := boundary
      rw [stopped] at edge
      exact False.elim (List.not_mem_nil edge)

/-- An executed statement cannot be the expression at which a generalized
initializer stops. Its scope is inherited from the actual body entry. -/
theorem LocalLambdaLexicalPath.statement_scope {source : TypedSource} {roots : List NodeId}
    {statement : StatementId} (path : LocalLambdaLexicalPath source roots (.statement statement))
    {entry : List TypeVarId}
    (initial : ∀ root ∈ roots, ∃ variables, ResidualScopePath source root variables ∧
      variables ⊆ entry) :
    ∃ variables, ResidualScopePath source (.statement statement) variables ∧ variables ⊆ entry := by
  obtain ⟨variables, scope, inherited | boundary⟩ := path.scope initial
  · exact ⟨variables, scope, inherited⟩
  · obtain ⟨_, _, _, _, _, _, same, _⟩ := boundary
    cases same

end Solcore.Frontend.SourceSpecializationWorklist

namespace Solcore.Frontend.SourceSpecializationWorklist
open SourceInference TypeSystem SourceSpecialization

/-- Entry evidence is about these actual body roots and a concrete substitution
key set. It is threaded through allocation and invocation, not assumed globally. -/
def ResidualEntryCovered (source : TypedSource) (roots : List NodeId)
    (domain : List TypeVarId) : Prop :=
  ∀ root ∈ roots, ∃ variables, ResidualScopePath source root variables ∧ variables ⊆ domain

def CapturedResidualScope (source : TypedSource) (initializer : ExpressionId)
    (own lexical : List TypeVarId) : Prop :=
  ∃ variables, ResidualScopePath source (.expression initializer) variables ∧
    ∀ metavariable ∈ variables, metavariable ∈ own ∨ metavariable ∈ lexical

theorem ResidualEntryCovered.named (source : TypedSource) (domain : List TypeVarId) :
    ResidualEntryCovered source source.roots domain := by
  intro root member
  exact ⟨[], .root member, by simp⟩

/-- A real let reached in this invocation inherits the entry scope. Its own
quantifiers are added only to the captured initializer. -/
theorem ResidualEntryCovered.capture {source : TypedSource} {roots : List NodeId}
    {domain : List TypeVarId} (covered : ResidualEntryCovered source roots domain)
    {id : StatementId} (path : LocalLambdaLexicalPath source roots (.statement id))
    {statement : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (found : source.lookupNode? id.occurrence = some (.statement statement))
    (form : statement.form = .letDecl binder (some initializer)) :
    CapturedResidualScope source initializer binder.scheme.quantified domain := by
  obtain ⟨before, scope, inherited⟩ := path.statement_scope covered
  have edge := localLambdaLexicalChildren_initialized found form
  obtain ⟨variables, scheduled⟩ := localLambdaLexicalChildren_residual edge before
  refine ⟨variables, .child scope scheduled, ?_⟩
  intro metavariable present
  by_cases old : metavariable ∈ before
  · exact .inr (inherited old)
  · obtain ⟨otherStatement, otherBinder, otherInitializer, otherFound, otherForm,
      _, owned⟩ := residualScopeChildren_new_quantifier scheduled present old
    have sameStatement : otherStatement = statement :=
      Node.statement.inj (Option.some.inj (otherFound.symm.trans found))
    subst otherStatement
    have sameBinder : otherBinder = binder :=
      (StatementForm.letDecl.inj (otherForm.symm.trans form)).1
    exact .inl (sameBinder ▸ owned)

/-- Invoking the captured lambda adds its own keys to the saved lexical keys.
The real lambda body edges preserve that scope; unrelated table nodes play no role. -/
theorem CapturedResidualScope.body {source : TypedSource} {initializer : ExpressionId}
    {own lexical current : List TypeVarId}
    (captured : CapturedResidualScope source initializer own lexical)
    (keys : ∀ metavariable, metavariable ∈ own ∨ metavariable ∈ lexical → metavariable ∈ current)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : source.lookupNode? initializer.occurrence = some (.expression node))
    (form : node.form = .lambda parameters result body) :
    ResidualEntryCovered source (body.map NodeId.statement) current := by
  obtain ⟨before, scope, inherited⟩ := captured
  intro child member
  have actual : child ∈ expressionChildNodeIds node := by
    rw [expressionChildNodeIds_eq_references]
    simpa only [form, ExpressionForm.references] using member
  have scheduledId : child ∈ (residualScopeChildren source (.expression initializer) before).map Prod.fst := by
    rw [residualScopeChildren_ids]
    simpa only [NodeId.occurrenceId, found] using actual
  obtain ⟨pair, scheduled, same⟩ := List.mem_map.mp scheduledId
  have edge : (child, pair.2) ∈ residualScopeChildren source (.expression initializer) before :=
    same ▸ scheduled
  refine ⟨pair.2, .child scope edge, ?_⟩
  intro metavariable present
  by_cases old : metavariable ∈ before
  · exact keys metavariable (inherited metavariable old)
  · obtain ⟨statement, binder, initializer, impossible, _, _, _⟩ :=
      residualScopeChildren_new_quantifier edge present old
    simp only [NodeId.occurrenceId, found] at impossible
    cases impossible

end Solcore.Frontend.SourceSpecializationWorklist
