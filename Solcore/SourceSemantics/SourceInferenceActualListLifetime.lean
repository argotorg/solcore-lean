import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeConstructorSteps
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForSteps

/-! Exact child edges lift lifetimes through ordered expression and statement lists. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem expressionsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {initial : State} {head : InferredExpression × State} {result : List InferredExpression × State}
    (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial result.1 result.2).Inputs)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  cases tailAccepted : inferExprsFuel fuel context sources head.2 with
  | error error => simp [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.expressions_head inputs.ready inputs.wellFormed inputs.catalog headAccepted tailAccepted accepted

private theorem constructorArgumentsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {result : List InferredExpression × State}
    (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial result.1 result.2).Inputs)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 with
  | error error => simp [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.constructorArguments_head inputs.ready inputs.wellFormed inputs.catalog inputs.bounds headAccepted tailAccepted accepted

private theorem statementsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {head : StatementResult} {result : BlockResult}
    (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: sources) expectedReturn initial = .ok result)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases sources with
  | nil => exact lifetime.statements_single headAccepted accepted
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
    | ok tail => exact lifetime.statements_head inputs.ready inputs.wellFormed inputs.catalog inputs.bounds headAccepted tailAccepted accepted

private theorem forItemsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem} {sources : List Syntax.ForItem}
    {initial : State} {head : ForItemForm × State} {result : InferredForItems}
    (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases tailAccepted : inferForItemsFuel fuel context sources head.2 with
  | error error => simp [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.forItems_head inputs.ready inputs.wellFormed inputs.catalog headAccepted tailAccepted accepted

namespace ChildStep

theorem lifetime_expressions
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (step : ChildStep (.expressions fuel context sources initial values final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final (values.map (·.type)) := by
  cases step with
  | expressions_head accepted headAccepted => exact expressionsHead inputs accepted headAccepted lifetime
  | expressions_tail accepted headAccepted tailAccepted =>
      exact lifetime.expressions_tail inputs.ready inputs.catalog headAccepted tailAccepted accepted

theorem lifetime_constructorArguments
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr} {expectedTypes : List Ty}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expectedTypes initial values final).Inputs)
    (step : ChildStep (.constructorArguments fuel context sources expectedTypes initial values final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final (values.map (·.type)) := by
  cases step with
  | constructorArguments_head accepted headAccepted => exact constructorArgumentsHead inputs accepted headAccepted lifetime
  | constructorArguments_tail accepted headAccepted tailAccepted =>
      exact lifetime.constructorArguments_tail inputs.ready inputs.catalog inputs.bounds headAccepted tailAccepted accepted

theorem lifetime_constructorApplication
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr} {expected : Option Ty}
    {initial final : State} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final).Inputs)
    (step : ChildStep (.constructorApplication fuel context source id instantiation arguments expected initial value final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [value.type] := by
  cases step with
  | constructorApplication_arguments accepted _ fitting childAccepted =>
      cases expected <;> exact lifetime.constructorApplication_arguments inputs.ready inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 fitting childAccepted accepted

theorem lifetime_statements
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement} {expected : Ty}
    {initial : State} {result : BlockResult} {child : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expected initial result).Inputs)
    (step : ChildStep (.statements fuel context sources expected initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step with
  | statements_head accepted headAccepted => exact statementsHead inputs accepted headAccepted lifetime
  | statements_tail accepted nonempty headAccepted tailAccepted =>
      rename_i rest _ _
      cases rest with
      | nil => exact False.elim (nonempty rfl)
      | cons next rest => exact lifetime.statements_tail inputs.ready inputs.catalog inputs.bounds headAccepted tailAccepted accepted

theorem lifetime_forItems
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {child : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (step : ChildStep (.forItems fuel context sources initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases step with
  | forItems_head accepted headAccepted => exact forItemsHead inputs accepted headAccepted lifetime
  | forItems_tail accepted headAccepted tailAccepted =>
      exact lifetime.forItems_tail inputs.ready inputs.catalog headAccepted tailAccepted accepted

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
