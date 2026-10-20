import Solcore.SourceSemantics.SourceInferenceActualExpressionInputs
import Solcore.SourceSemantics.SourceInferenceActualExpressionEntryInputs
import Solcore.SourceSemantics.SourceInferenceActualListCallInputs
import Solcore.SourceSemantics.SourceInferenceActualMutableCallInputs
import Solcore.SourceSemantics.SourceInferenceActualStatementCallInputs
import Solcore.SourceSemantics.SourceInferenceActualMatchCallInputs

/-! Ordinary checker inputs follow every actual child edge from one root. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.inputs {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child) : child.Inputs := by
  cases parent with
  | expression =>
      cases step
      all_goals first
      | solve | apply ActualExpressionInputs.expression_group <;> assumption
      | solve | apply ActualExpressionInputs.expression_tuple <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_arguments <;> assumption
      | solve | apply ActualExpressionInputs.expression_unary <;> assumption
      | solve | apply ActualExpressionInputs.expression_binary_left <;> assumption
      | solve | apply ActualExpressionInputs.expression_index_base <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_condition <;> assumption
      | solve | apply ActualExpressionInputs.expression_binary_right <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_callee <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_then <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_else <;> assumption
      | solve | apply ActualExpressionInputs.expression_index_key <;> assumption
      | solve | apply ActualExpressionInputs.expression_lambda_body <;> assumption
      | solve | apply ActualExpressionInputs.expression_contextual_constructor <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_constructor <;> assumption
      | solve | apply ActualExpressionInputs.expression_field_constructor <;> assumption
  | constructorApplication => exact ChildStep.inputs_constructorApplication inputs step
  | constructorArguments => exact ChildStep.inputs_constructorArguments inputs step
  | statements => exact ChildStep.inputs_statements inputs step
  | statement => exact ChildStep.inputs_statement inputs step
  | forItems => exact ChildStep.inputs_forItems inputs step
  | forItem => exact ChildStep.inputs_forItem inputs step
  | place => exact ChildStep.inputs_place inputs step
  | assignedValue => exact ChildStep.inputs_assignedValue inputs step
  | expressions => exact ChildStep.inputs_expressions inputs step
  | matchCases => exact ChildStep.inputs_matchCases inputs step

theorem CallOccurrence.inputs {root call : CallIndex}
    (inputs : root.Inputs) (occurrence : CallOccurrence root call) : call.Inputs := by
  induction occurrence with
  | root _ => exact inputs
  | child _ step ih => exact step.inputs ih

end Solcore.SourceSemantics.SourceInferenceExecution
