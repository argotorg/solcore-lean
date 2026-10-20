import Solcore.SourceSemantics.SourceInferenceActualTerminalProgress
import Solcore.SourceSemantics.SourceInferenceActualListProgress
import Solcore.SourceSemantics.SourceInferenceActualBranchProgress
import Solcore.SourceSemantics.SourceInferenceActualForProgress
import Solcore.SourceSemantics.SourceInferenceActualMutableProgress
import Solcore.SourceSemantics.SourceInferenceActualMatchProgress

/-! Every non-expression child has its actual suffix substitution continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

def CallIndex.NonExpression : CallIndex → Prop
  | .expression .. => False
  | _ => True

theorem ChildStep.progress_nonexpression {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child)
    (nonexpression : parent.NonExpression) :
    child.final.InferenceProgress parent.final := by
  cases step with
  | expression_group accepted form allocation child =>
      exact False.elim nonexpression
  | expression_tuple accepted form allocation child =>
      exact False.elim nonexpression
  | expressions_head accepted head =>
      exact ActualSuffixProgress.expressions_head accepted head inputs
  | expressions_tail accepted head tail =>
      exact ActualSuffixProgress.expressions_tail accepted head tail inputs
  | statements_head accepted child =>
      exact ActualSuffixProgress.statements_head accepted child inputs
  | statements_tail accepted nonempty headAccepted child =>
      exact ActualSuffixProgress.statements_tail accepted nonempty headAccepted child inputs
  | statement_initializer accepted form allocation annotation child =>
      exact ActualSuffixProgress.statement_initializer accepted form allocation annotation child inputs
  | statement_return accepted form allocation child =>
      exact ActualSuffixProgress.statement_return accepted form allocation child inputs
  | statement_expression accepted form allocation child =>
      exact ActualSuffixProgress.statement_expression accepted form allocation child inputs
  | statement_block accepted form allocation child =>
      exact ActualSuffixProgress.statement_block accepted form allocation child inputs
  | statement_if_condition accepted form allocation child =>
      exact ActualSuffixProgress.statement_if_condition accepted form allocation child inputs
  | statement_if_then accepted form allocation conditionAccepted child =>
      exact ActualSuffixProgress.statement_if_then accepted form allocation conditionAccepted child inputs
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      exact ActualSuffixProgress.statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child inputs
  | statement_assignment accepted form allocation child =>
      exact ActualSuffixProgress.statement_assignment accepted form allocation child inputs
  | statement_bitnot accepted form allocation child =>
      exact ActualSuffixProgress.statement_bitnot accepted form allocation child inputs
  | statement_while_condition accepted form allocation child =>
      exact ActualSuffixProgress.statement_while_condition accepted form allocation child inputs
  | statement_while_body accepted form allocation conditionAccepted child =>
      exact ActualSuffixProgress.statement_while_body accepted form allocation conditionAccepted child inputs
  | statement_for_initializer accepted form allocation child =>
      exact ActualSuffixProgress.statement_for_initializer accepted form allocation child inputs
  | statement_for_condition accepted form allocation initializerAccepted child =>
      exact ActualSuffixProgress.statement_for_condition accepted form allocation initializerAccepted child inputs
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      exact ActualSuffixProgress.statement_for_body accepted form allocation initializerAccepted conditionAccepted child inputs
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      exact ActualSuffixProgress.statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child inputs
  | forItems_head accepted child =>
      exact ActualSuffixProgress.forItems_head accepted child inputs
  | forItems_tail accepted headAccepted child =>
      exact ActualSuffixProgress.forItems_tail accepted headAccepted child inputs
  | forItem_initializer accepted form annotation child =>
      exact ActualSuffixProgress.forItem_initializer accepted form annotation child inputs
  | forItem_expression accepted form child =>
      exact ActualSuffixProgress.forItem_expression accepted form child inputs
  | forItem_assignment accepted form child =>
      exact ActualSuffixProgress.forItem_assignment accepted form child inputs
  | forItem_bitnot accepted form child =>
      exact ActualSuffixProgress.forItem_bitnot accepted form child inputs
  | assignedValue_place accepted child =>
      exact ActualSuffixProgress.assignedValue_place accepted child inputs
  | assignedValue_value accepted targetAccepted fitting child =>
      exact ActualSuffixProgress.assignedValue_value accepted targetAccepted fitting child inputs
  | place_group accepted form child =>
      exact ActualSuffixProgress.place_group accepted form child inputs
  | place_index_base accepted form child =>
      exact ActualSuffixProgress.place_index_base accepted form child inputs
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      exact ActualSuffixProgress.place_index_key accepted form baseAccepted keyFresh valueFresh fitting child inputs
  | constructorApplication_arguments accepted arity fitting child =>
      exact ActualSuffixProgress.constructorApplication_arguments accepted arity fitting child inputs
  | constructorArguments_head accepted child =>
      exact ActualSuffixProgress.constructorArguments_head accepted child inputs
  | constructorArguments_tail accepted headAccepted child =>
      exact ActualSuffixProgress.constructorArguments_tail accepted headAccepted child inputs
  | expression_unary accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_left accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_right accepted form allocation leftAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_condition accepted form allocation child =>
      exact False.elim nonexpression
  | expression_conditional_then accepted form allocation conditionAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted child =>
      exact False.elim nonexpression
  | expression_lambda_body accepted form allocation parametersAccepted prefixFacts child =>
      exact False.elim nonexpression
  | expression_index_base accepted form allocation child =>
      exact False.elim nonexpression
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
      exact False.elim nonexpression
  | expression_call_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | expression_call_arguments accepted form allocation nonconstructor child =>
      exact False.elim nonexpression
  | expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect child =>
      exact False.elim nonexpression
  | expression_contextual_constructor accepted form allocation selected child =>
      exact False.elim nonexpression
  | expression_field_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | matchCases_body accepted patternAccepted child =>
      exact ActualSuffixProgress.matchCases_body accepted patternAccepted child inputs
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      exact ActualSuffixProgress.matchCases_tail accepted patternAccepted bodyAccepted child inputs
  | statement_match_single accepted form allocation single child =>
      exact ActualSuffixProgress.statement_match_single accepted form allocation single child inputs
  | statement_match_many accepted form allocation multiple child =>
      exact ActualSuffixProgress.statement_match_many accepted form allocation multiple child inputs
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      exact ActualSuffixProgress.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child inputs
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      exact ActualSuffixProgress.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child inputs

end Solcore.SourceSemantics.SourceInferenceExecution
