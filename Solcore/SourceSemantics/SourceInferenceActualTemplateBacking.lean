import Solcore.SourceSemantics.SourceInferenceActualExpressionTemplateBacking
import Solcore.SourceSemantics.SourceInferenceActualOtherTemplateBacking
import Solcore.SourceSemantics.SourceInferenceActualStatementTemplateBacking

/-! Actual child calls inherit raw witnesses for their active local templates.
The root-to-child theorem follows the original accepted call graph. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open SourceInferenceSoundness.ProtectedVariables

theorem ChildStep.liveTemplatesBacked {parent child : CallIndex}
    (step : ChildStep parent child) (inputs : parent.Inputs)
    (backed : LiveTemplatesBacked parent.initial) :
    LiveTemplatesBacked child.initial := by
  cases step
  all_goals first
  | solve | apply ActualTemplateBacking.expression_group <;> assumption
  | solve | apply ActualTemplateBacking.expression_tuple <;> assumption
  | solve | apply ActualTemplateBacking.expressions_head <;> assumption
  | solve | apply ActualTemplateBacking.expressions_tail <;> assumption
  | solve | apply ActualTemplateBacking.statements_head <;> assumption
  | solve | apply ActualTemplateBacking.statements_tail <;> assumption
  | solve | apply ActualTemplateBacking.statement_initializer <;> assumption
  | solve | apply ActualTemplateBacking.statement_return <;> assumption
  | solve | apply ActualTemplateBacking.statement_expression <;> assumption
  | solve | apply ActualTemplateBacking.statement_block <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_then <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_else <;> assumption
  | solve | apply ActualTemplateBacking.statement_assignment <;> assumption
  | solve | apply ActualTemplateBacking.statement_bitnot <;> assumption
  | solve | apply ActualTemplateBacking.statement_while_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_while_body <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_initializer <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_body <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_post <;> assumption
  | solve | apply ActualTemplateBacking.forItems_head <;> assumption
  | solve | apply ActualTemplateBacking.forItems_tail <;> assumption
  | solve | apply ActualTemplateBacking.forItem_initializer <;> assumption
  | solve | apply ActualTemplateBacking.forItem_expression <;> assumption
  | solve | apply ActualTemplateBacking.forItem_assignment <;> assumption
  | solve | apply ActualTemplateBacking.forItem_bitnot <;> assumption
  | solve | apply ActualTemplateBacking.assignedValue_place <;> assumption
  | solve | apply ActualTemplateBacking.assignedValue_value <;> assumption
  | solve | apply ActualTemplateBacking.place_group <;> assumption
  | solve | apply ActualTemplateBacking.place_index_base <;> assumption
  | solve | apply ActualTemplateBacking.place_index_key <;> assumption
  | solve | apply ActualTemplateBacking.constructorApplication_arguments <;> assumption
  | solve | apply ActualTemplateBacking.constructorArguments_head <;> assumption
  | solve | apply ActualTemplateBacking.constructorArguments_tail <;> assumption
  | solve | apply ActualTemplateBacking.expression_unary <;> assumption
  | solve | apply ActualTemplateBacking.expression_binary_left <;> assumption
  | solve | apply ActualTemplateBacking.expression_binary_right <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_condition <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_then <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_else <;> assumption
  | solve | apply ActualTemplateBacking.expression_lambda_body <;> assumption
  | solve | apply ActualTemplateBacking.expression_index_base <;> assumption
  | solve | apply ActualTemplateBacking.expression_index_key <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_constructor <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_arguments <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_callee <;> assumption
  | solve | apply ActualTemplateBacking.expression_contextual_constructor <;> assumption
  | solve | apply ActualTemplateBacking.expression_field_constructor <;> assumption
  | solve | apply ActualTemplateBacking.matchCases_body <;> assumption
  | solve | apply ActualTemplateBacking.matchCases_tail <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_single <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_many <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_cases <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_default <;> assumption

theorem CallOccurrence.liveTemplatesBacked {root call : CallIndex}
    (inputs : root.Inputs) (backed : LiveTemplatesBacked root.initial)
    (here : CallOccurrence root call) : LiveTemplatesBacked call.initial := by
  induction here with
  | root _ => exact backed
  | child parent step ih => exact step.liveTemplatesBacked (parent.inputs inputs) ih

end Solcore.SourceSemantics.SourceInferenceExecution
