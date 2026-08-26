import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleModule
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The complete module reduction preserves its exact top-item token plan. -/
theorem module_tokenPlanSound :
    GrammarRuleTokenPlanSound .module := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  exact RuleReduction.module_tokenPlanEvidence reduces inputEvidence

/-- All literal reductions preserve the exact scanned literal token. -/
theorem literal_tokenPlanSound :
    GrammarRuleTokenPlanSound .literal := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  exact RuleReduction.literal_tokenPlanEvidence reduces inputEvidence

/-- All assignment-operator reductions preserve the exact scanned symbol. -/
theorem assignmentOperator_tokenPlanSound :
    GrammarRuleTokenPlanSound .assignmentOperator := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  exact RuleReduction.assignmentOperator_tokenPlanEvidence
    reduces inputEvidence

/-- Qualified-name reductions preserve identifiers and separating dots. -/
theorem qualifiedName_tokenPlanSound :
    GrammarRuleTokenPlanSound .qualifiedName := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  exact RuleReduction.qualifiedName_tokenPlanEvidence reduces inputEvidence

/-- An instance method is the unchanged function-declaration child. -/
theorem instanceMethod_tokenPlanSound :
    GrammarRuleTokenPlanSound .instanceMethod := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | instanceMethod origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.instanceMethod)
        inputEvidence

/-- Every statement choice preserves the selected statement child's plan. -/
theorem statement_tokenPlanSound :
    GrammarRuleTokenPlanSound .statement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | statementLet origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementLet)
        inputEvidence
  | statementReturn origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementReturn)
        inputEvidence
  | statementMatch origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementMatch)
        inputEvidence
  | statementIf origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementIf)
        inputEvidence
  | statementFor origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementFor)
        inputEvidence
  | statementAssembly origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementAssembly)
        inputEvidence
  | statementBlock origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementBlock)
        inputEvidence
  | statementBreak origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementBreak)
        inputEvidence
  | statementContinue origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementContinue)
        inputEvidence
  | statementAssignment origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementAssignment)
        inputEvidence
  | statementExpression origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.statementExpression)
        inputEvidence

/-- Match-arm statements preserve the selected statement plan. -/
theorem armStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .armStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | armStatement origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.armStatement)
        inputEvidence

/-- A terminal expression is the unchanged expression child. -/
theorem terminalExpression_tokenPlanSound :
    GrammarRuleTokenPlanSound .terminalExpression := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | terminalExpression origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.terminalExpression)
        inputEvidence

/-- The expression root is the unchanged annotation-expression child. -/
theorem expression_tokenPlanSound :
    GrammarRuleTokenPlanSound .expression := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | expression origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.expression)
        inputEvidence

end Solcore.Surface.Multi
