import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

/-! Unique-occurrence inversion for independent source for statements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForSourceViews

open Frontend Frontend.SourceInference

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem success
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ loopContext loopFinalContext loopEnvironment initialized loopOutcome,
      outcome = Dynamic.restoreControl environment loopOutcome ∧
      Dynamic.ForItemsExecute program context evidence source environment before items loopContext loopEnvironment initialized ∧
      Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized condition post statements loopFinalContext loopOutcome after := by
  have formShape := shape unique contains form
  clear contains form
  cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, _, _, rfl, by assumption, by assumption⟩

theorem fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    (∃ finalContext, Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) ∨
    (∃ loopContext loopEnvironment initialized,
      Dynamic.ForItemsExecute program context evidence source environment before items loopContext loopEnvironment initialized ∧
      Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized condition post statements reason after) := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := formShape _ (by assumption); simp_all
  · exact .inl ⟨_, by assumption⟩
  · exact .inr ⟨_, _, _, by assumption, by assumption⟩

end Solcore.SourceSemantics.CoreLowering.ForSourceViews
