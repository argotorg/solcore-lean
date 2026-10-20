import Solcore.Frontend.SourceInference.Expression

/-! Exact inputs and outputs of the eleven mutually recursive inference calls.
These indices contain execution data, not a source typing or privacy law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

inductive CallIndex where
  | expression (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (expected : Option Ty) (initial : State) (value : InferredExpression) (final : State)
  | constructorApplication (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (id : ExpressionId) (instantiation : DataConstructorInstantiation) (arguments : List Syntax.Expr)
      (expected : Option Ty) (initial : State) (value : InferredExpression) (final : State)
  | constructorArguments (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
      (expectedTypes : List Ty) (initial : State) (values : List InferredExpression) (final : State)
  | statements (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Statement)
      (expectedReturn : Ty) (initial : State) (result : BlockResult)
  | statement (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Statement)
      (expectedReturn : Ty) (initial : State) (result : StatementResult)
  | forItems (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.ForItem)
      (initial : State) (result : InferredForItems)
  | forItem (fuel : Nat) (context : SourceInference.Context) (source : Syntax.ForItem)
      (initial : State) (value : ForItemForm) (final : State)
  | place (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (initial : State) (value : PlaceResolution) (final : State)
  | assignedValue (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
      (operator : Syntax.ValueAssignOp) (value : Syntax.Expr) (initial : State)
      (assignment : AssignmentResolution) (inferred : InferredExpression) (final : State)
  | expressions (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
      (initial : State) (values : List InferredExpression) (final : State)
  | matchCases (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
      (saved : LexicalScope) (cases : List Syntax.MatchCase) (initial : State) (result : MatchCasesResult)

namespace CallIndex

def Accepted : CallIndex → Prop
  | .expression fuel context source expected initial value final =>
      inferExprFuel fuel context source expected initial = .ok (value, final)
  | .constructorApplication fuel context source id instantiation arguments expected initial value final =>
      inferConstructorApplicationFuel fuel context source id instantiation arguments expected initial = .ok (value, final)
  | .constructorArguments fuel context sources expectedTypes initial values final =>
      inferConstructorArgumentsFuel fuel context sources expectedTypes initial = .ok (values, final)
  | .statements fuel context sources expectedReturn initial result =>
      inferStatementsFuel fuel context sources expectedReturn initial = .ok result
  | .statement fuel context source expectedReturn initial result =>
      inferStatementFuel fuel context source expectedReturn initial = .ok result
  | .forItems fuel context sources initial result =>
      inferForItemsFuel fuel context sources initial = .ok result
  | .forItem fuel context source initial value final =>
      inferForItemFuel fuel context source initial = .ok (value, final)
  | .place fuel context source initial value final =>
      inferPlaceFuel fuel context source initial = .ok (value, final)
  | .assignedValue fuel context target operator value initial assignment inferred final =>
      inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final)
  | .expressions fuel context sources initial values final =>
      inferExprsFuel fuel context sources initial = .ok (values, final)
  | .matchCases fuel context scrutineeType expectedReturn saved cases initial result =>
      inferMatchCasesFuel fuel context scrutineeType expectedReturn saved cases initial = .ok result

def initial : CallIndex → State
  | .expression _ _ _ _ state _ _
  | .constructorApplication _ _ _ _ _ _ _ state _ _
  | .constructorArguments _ _ _ _ state _ _
  | .statements _ _ _ _ state _
  | .statement _ _ _ _ state _
  | .forItems _ _ _ state _
  | .forItem _ _ _ state _ _
  | .place _ _ _ state _ _
  | .assignedValue _ _ _ _ _ state _ _ _
  | .expressions _ _ _ state _ _
  | .matchCases _ _ _ _ _ _ state _ => state

def final : CallIndex → State
  | .expression _ _ _ _ _ _ state
  | .constructorApplication _ _ _ _ _ _ _ _ _ state
  | .constructorArguments _ _ _ _ _ _ state
  | .forItem _ _ _ _ _ state
  | .place _ _ _ _ _ state
  | .assignedValue _ _ _ _ _ _ _ _ state
  | .expressions _ _ _ _ _ state => state
  | .statements _ _ _ _ _ result => result.state
  | .statement _ _ _ _ _ result => result.state
  | .forItems _ _ _ _ result => result.state
  | .matchCases _ _ _ _ _ _ _ result => result.state

end CallIndex
end Solcore.SourceSemantics.SourceInferenceExecution
