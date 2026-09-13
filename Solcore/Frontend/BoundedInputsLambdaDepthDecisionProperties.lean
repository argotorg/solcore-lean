import Solcore.Frontend.BoundedInputsLambdaDepth
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties

/- Exact outer-call decisions under two supplied successful finite input runs.
The actual saved body is data-gated; its success is not an admission premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore argumentStore : List RuntimeValue}
variable {calleeBudget argumentBudget : Nat} {argumentValue : RuntimeValue}
variable (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
  callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
variable (supplied : evaluateClosedSourceExpression? argumentBudget callerOwner callerNames callerCaptured calleeStore
  argument = some (argumentValue,argumentStore))
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape bodyFragment selected supplied

/-- A sufficiently deep call with supplied finite inputs returns each original full endpoint. -/
theorem boundedInputsLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied original enough⟩

/-- Whole Option stability includes actual selected-body failure under successful inputs. -/
theorem boundedInputsLambda_evaluate_depth_stable
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem boundedInputsLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := boundedInputsLambda_evaluates_at_depthBound shape bodyFragment selected supplied original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- Two supplied input runs and actual saved syntax bound one outer-call search.
This does not find child budgets or decide unsuccessful callee or argument inputs. -/
theorem boundedInputsLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (boundedInputsLambdaDepthBound calleeBudget argumentBudget body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (boundedInputsLambda_evaluate_depth_none_iff shape bodyFragment selected supplied
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
