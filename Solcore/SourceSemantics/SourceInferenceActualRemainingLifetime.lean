import Solcore.SourceSemantics.SourceInferenceActualListLifetime
import Solcore.SourceSemantics.SourceInferenceActualMutableLifetime
import Solcore.SourceSemantics.SourceInferenceActualStatementLifetime
import Solcore.SourceSemantics.SourceInferenceActualForLifetime

/-! All non-expression edges except enclosing generalization use checker evidence alone.
The two declaration edges additionally consume their actual compiled template scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

def CallIndex.Initializes : CallIndex → Prop
  | .statement _ _ source _ _ _ => match source.value with
    | .letDecl _ _ (some _) => True
    | _ => False
  | .forItem _ _ source _ _ _ => match source.value with
    | .letDecl _ _ (some _) => True
    | _ => False
  | _ => False

namespace ChildStep

theorem lifetime_statement_noninitializer
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {expected : Ty}
    {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child)
    (noninitializer : ¬ (CallIndex.statement fuel context source expected initial result).Initializes)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step
  all_goals first
  | solve | apply False.elim; apply noninitializer; simp_all [CallIndex.Initializes]
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

theorem lifetime_forItem_noninitializer
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child)
    (noninitializer : ¬ (CallIndex.forItem fuel context source initial value final).Initializes)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [] := by
  cases step
  all_goals first
  | solve | apply False.elim; apply noninitializer; simp_all [CallIndex.Initializes]
  | solve | apply ActualStatementLifetime.forItem_expression <;> assumption
  | solve | apply ActualStatementLifetime.forItem_assignment <;> assumption
  | solve | apply ActualStatementLifetime.forItem_bitnot <;> assumption

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
