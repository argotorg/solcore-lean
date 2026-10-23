import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationResidualEntry

/-! Actual initialized statements capture the scope of their own invocation.
The compiler's substitution preserves the quantified variables and occurrence
identities used by this evidence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableBodyMetadataViews

private theorem statement_node {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node) :
    source.lookupNode? id.occurrence = some (.statement node) := by
  unfold TypedSource.lookupStatement? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | expression => simp [selected] at found
    | statement original =>
      have same : original = node := by simpa [selected] using found
      simp only [same]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : BodyRelation} {index : Index compiled bodyRelation}

theorem Index.ResidualEntry.capture_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer)) :
    CapturedResidualScope index.originalSource initializer
      binder.scheme.quantified index.active.domain := by
  rw [index.compiler_original, lookupStatement_apply] at found
  obtain ⟨original, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  rcases original with ⟨originalId, span, type, actual⟩
  cases actual <;> simp only [StatementNode.applySubstitution,
    StatementForm.applySubstitution] at form <;> try contradiction
  rename_i rawBinder rawInitializer
  obtain ⟨rfl, sameInitializer⟩ := StatementForm.letDecl.inj form
  subst rawInitializer
  exact entry.covered.capture (binder := rawBinder) site.lexical (statement_node selected) rfl

private theorem initialized_item_before {active : Substitution} {items : List ForItemForm}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ items.map (ForItemForm.applySubstitution active)) :
    ∃ original, .letDecl original (some initializer) ∈ items ∧
      original.scheme.quantified = binder.scheme.quantified := by
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  cases original <;> simp only [ForItemForm.applySubstitution] at same <;> try contradiction
  rename_i rawBinder rawInitializer
  obtain ⟨rfl, sameInitializer⟩ := ForItemForm.letDecl.inj same
  subst rawInitializer
  exact ⟨rawBinder, present, rfl⟩

theorem Index.ResidualEntry.capture_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ initializers ++ post) :
    CapturedResidualScope index.originalSource initializer
      binder.scheme.quantified index.active.domain := by
  rw [index.compiler_original, lookupStatement_apply] at found
  obtain ⟨original, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  rcases original with ⟨originalId, span, type, actual⟩
  cases actual <;> simp only [StatementNode.applySubstitution,
    StatementForm.applySubstitution] at form <;> try contradiction
  obtain ⟨rfl, rfl, rfl, rfl⟩ := StatementForm.forLoop.inj form
  rw [← List.map_append] at member
  obtain ⟨rawBinder, present, same⟩ := initialized_item_before member
  rw [← same]
  exact ResidualScopeReachability.capture_header entry.covered site.lexical selected rfl present

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
