import Solcore.SourceSemantics.SourceInferenceActualNonExpressionProgress
import Solcore.SourceSemantics.SourceInferenceActualTerminalBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualListBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualBranchBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualForBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualMutableBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualMatchBinderRetention

/-! Every non-expression child preserves all initialized binders through its actual suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.nonexpression_binders_retained {parent child : CallIndex}
    (step : ChildStep parent child)
    (nonexpression : parent.NonExpression) :
    Frontend.SourceInference.LocalGeneralizationEvents.BindersRetained child.final.nodes parent.final.nodes := by
  cases step with
  | expression_group accepted form allocation child =>
      exact False.elim nonexpression
  | expression_tuple accepted form allocation child =>
      exact False.elim nonexpression
  | expressions_head accepted head =>
      exact ActualBinderRetention.expressions_head accepted head
  | expressions_tail accepted head tail =>
      exact ActualBinderRetention.expressions_tail accepted head tail
  | statements_head accepted child =>
      exact ActualBinderRetention.statements_head accepted child
  | statements_tail accepted nonempty headAccepted child =>
      exact ActualBinderRetention.statements_tail accepted nonempty headAccepted child
  | statement_initializer accepted form allocation annotation child =>
      exact ActualBinderRetention.statement_initializer accepted form allocation annotation child
  | statement_return accepted form allocation child =>
      exact ActualBinderRetention.statement_return accepted form allocation child
  | statement_expression accepted form allocation child =>
      exact ActualBinderRetention.statement_expression accepted form allocation child
  | statement_block accepted form allocation child =>
      exact ActualBinderRetention.statement_block accepted form allocation child
  | statement_if_condition accepted form allocation child =>
      exact ActualBinderRetention.statement_if_condition accepted form allocation child
  | statement_if_then accepted form allocation conditionAccepted child =>
      exact ActualBinderRetention.statement_if_then accepted form allocation conditionAccepted child
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      exact ActualBinderRetention.statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  | statement_assignment accepted form allocation child =>
      exact ActualBinderRetention.statement_assignment accepted form allocation child
  | statement_bitnot accepted form allocation child =>
      exact ActualBinderRetention.statement_bitnot accepted form allocation child
  | statement_while_condition accepted form allocation child =>
      exact ActualBinderRetention.statement_while_condition accepted form allocation child
  | statement_while_body accepted form allocation conditionAccepted child =>
      exact ActualBinderRetention.statement_while_body accepted form allocation conditionAccepted child
  | statement_for_initializer accepted form allocation child =>
      exact ActualBinderRetention.statement_for_initializer accepted form allocation child
  | statement_for_condition accepted form allocation initializerAccepted child =>
      exact ActualBinderRetention.statement_for_condition accepted form allocation initializerAccepted child
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      exact ActualBinderRetention.statement_for_body accepted form allocation initializerAccepted conditionAccepted child
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      exact ActualBinderRetention.statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child
  | forItems_head accepted child =>
      exact ActualBinderRetention.forItems_head accepted child
  | forItems_tail accepted headAccepted child =>
      exact ActualBinderRetention.forItems_tail accepted headAccepted child
  | forItem_initializer accepted form annotation child =>
      exact ActualBinderRetention.forItem_initializer accepted form annotation child
  | forItem_expression accepted form child =>
      exact ActualBinderRetention.forItem_expression accepted form child
  | forItem_assignment accepted form child =>
      exact ActualBinderRetention.forItem_assignment accepted form child
  | forItem_bitnot accepted form child =>
      exact ActualBinderRetention.forItem_bitnot accepted form child
  | assignedValue_place accepted child =>
      exact ActualBinderRetention.assignedValue_place accepted child
  | assignedValue_value accepted targetAccepted fitting child =>
      exact ActualBinderRetention.assignedValue_value accepted targetAccepted fitting child
  | place_group accepted form child =>
      exact ActualBinderRetention.place_group accepted form child
  | place_index_base accepted form child =>
      exact ActualBinderRetention.place_index_base accepted form child
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      exact ActualBinderRetention.place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  | constructorApplication_arguments accepted arity fitting child =>
      exact ActualBinderRetention.constructorApplication_arguments accepted arity fitting child
  | constructorArguments_head accepted child =>
      exact ActualBinderRetention.constructorArguments_head accepted child
  | constructorArguments_tail accepted headAccepted child =>
      exact ActualBinderRetention.constructorArguments_tail accepted headAccepted child
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
      exact ActualBinderRetention.matchCases_body accepted patternAccepted child
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      exact ActualBinderRetention.matchCases_tail accepted patternAccepted bodyAccepted child
  | statement_match_single accepted form allocation single child =>
      exact ActualBinderRetention.statement_match_single accepted form allocation single child
  | statement_match_many accepted form allocation multiple child =>
      exact ActualBinderRetention.statement_match_many accepted form allocation multiple child
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      exact ActualBinderRetention.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      exact ActualBinderRetention.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child

end Solcore.SourceSemantics.SourceInferenceExecution
