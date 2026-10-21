import Solcore.SourceSemantics.SourceCompiledActualInitializerLifetime
import Solcore.SourceSemantics.SourceInferenceActualExpressionLifetime
import Solcore.SourceSemantics.SourceInferenceActualRemainingLifetime

/-! Every actual child lifetime reaches its actual parent. The two initialized
edges consume the same cached body and exact declaration receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized checkingFuel}
    {binder : TypedBinder} {initializerId : ExpressionId}
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializerId}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
namespace ChildStep
theorem lifetime_statement
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {expected : Ty}
    {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child)
    (here : selected.InferenceCall (.statement fuel context source expected initial result))
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step
  all_goals first
  | solve | apply ChildStep.lifetime_statement_initializer artifact checked position <;> assumption
  | solve | apply ActualStatementLifetime.statement_return <;> assumption
  | solve | apply ActualStatementLifetime.statement_expression <;> assumption
  | solve | apply ActualStatementLifetime.statement_block <;> assumption
  | solve | apply ActualStatementLifetime.statement_assignment <;> assumption
  | solve | apply ActualStatementLifetime.statement_bitnot <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_then <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_else <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_initializer <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_post <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_single <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_many <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_cases <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_default <;> assumption

theorem lifetime_forItem
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child)
    (here : selected.InferenceCall (.forItem fuel context source initial value final))
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [] := by
  cases step
  all_goals first
  | solve | apply ChildStep.lifetime_header_initializer artifact checked position <;> assumption
  | solve | apply ActualStatementLifetime.forItem_expression <;> assumption
  | solve | apply ActualStatementLifetime.forItem_assignment <;> assumption
  | solve | apply ActualStatementLifetime.forItem_bitnot <;> assumption

theorem lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {parent child : CallIndex}
    (here : selected.InferenceCall parent) (step : ChildStep parent child)
    (life : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event parent.initial.inference.next parent.final parent.outputTypes := by
  have inputs := selected.actualCall_inputs checked here
  cases parent with
  | expression => exact step.lifetime_expression inputs life
  | constructorApplication => exact step.lifetime_constructorApplication inputs life
  | constructorArguments => exact step.lifetime_constructorArguments inputs life
  | statements => exact step.lifetime_statements inputs life
  | statement => exact step.lifetime_statement artifact checked position inputs here life
  | forItems => exact step.lifetime_forItems inputs life
  | forItem => exact step.lifetime_forItem artifact checked position inputs here life
  | place => exact step.lifetime_place inputs life
  | assignedValue => exact step.lifetime_assignedValue inputs life
  | expressions => exact step.lifetime_expressions inputs life
  | matchCases => exact step.lifetime_matchCases inputs life

end ChildStep

theorem CallOccurrence.lifetime_at
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {earlier call : CallIndex} (reached : selected.InferenceCall earlier)
    (path : CallOccurrence earlier call)
    (life : GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes) :
    GeneralizationLifetime event earlier.initial.inference.next earlier.final earlier.outputTypes := by
  induction path with
  | root accepted => exact life
  | child prior step ih =>
      exact ih (step.lifetime artifact checked position (reached.trans prior) life)

theorem CallOccurrence.lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {call : CallIndex} (here : selected.InferenceCall call)
    (life : GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes) :
    GeneralizationLifetime event selected.inferenceCall.initial.inference.next
      selected.inferenceCall.final selected.inferenceCall.outputTypes := by
  induction here with
  | root accepted => exact life
  | child prior step ih =>
      exact ih (step.lifetime artifact checked position prior life)

end Solcore.SourceSemantics.SourceInferenceExecution
