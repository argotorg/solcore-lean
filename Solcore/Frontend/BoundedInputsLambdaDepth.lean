import Solcore.Frontend.ClosedSource

/- Both finite successful input runs are supplied, not discovered. The argument
starts from the actual callee store; only the selected saved body is data-gated.
No saved-body success is required outside an original successful endpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Compose supplied successful input budgets with the actual saved data-body depth. -/
def boundedInputsLambdaDepthBound (calleeBudget argumentBudget : Nat) (body : Syntax.Block) : Nat :=
  max calleeBudget (max argumentBudget (closedSourceDataBodyDepthBound body)) + 1

/-- Actual finite input endpoints fix the selected closure and its fresh body inputs. -/
theorem boundedInputsLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore argumentStore finalStore : List RuntimeValue}
    {calleeBudget argumentBudget : Nat} {argumentValue : RuntimeValue}
    (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
      callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
    (supplied : evaluateClosedSourceExpression? argumentBudget callerOwner callerNames callerCaptured calleeStore
      argument = some (argumentValue,argumentStore))
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : boundedInputsLambdaDepthBound calleeBudget argumentBudget body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  have independentCallee := evaluateClosedSourceExpression?_sound selected
  have independentArgument := evaluateClosedSourceExpression?_sound supplied
  unfold boundedInputsLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameCalleeStore⟩ := calleeEvaluation.deterministic independentCallee
      cases sameCallee; cases sameCalleeStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      obtain ⟨sameArgument,sameArgumentStore⟩ := argumentEvaluation.deterministic independentArgument
      cases sameArgument; cases sameArgumentStore
      have calleeRun := evaluateClosedSourceExpression?_monotone (by omega : calleeBudget ≤ budget) selected
      have argumentRun := evaluateClosedSourceExpression?_monotone (by omega : argumentBudget ≤ budget) supplied
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.BoundedInputsLambdaDepthDecisionProperties`
-/

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
