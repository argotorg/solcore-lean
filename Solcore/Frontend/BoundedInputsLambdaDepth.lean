import Solcore.Frontend.ClosedSourceDataBodyDepthProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

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
