import Solcore.Frontend.ClosedSourceDataDepthBoundProperties
import Solcore.Frontend.ClosedSourceDataBodyDepthProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- An independent original data-callee success selects the actual saved datum.
The explicit selection premise is not an unconditional callee decision. Caller
argument and fresh saved body retain every actual intermediate and final store. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Sufficient depth using admitted data callee/argument syntax and the selected saved body. -/
def dataCalleeLambdaDepthBound (callee argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max (closedSourceDataDepthBound callee)
    (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- The independently selected callee fixes actual saved fields and callee store.
No argument or body success is assumed except inside the original whole endpoint. -/
theorem dataCalleeLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (calleeFragment : ClosedSourceDataExpression callee)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore finalStore : List RuntimeValue}
    (selected : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      callee (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  unfold dataCalleeLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic selected
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := calleeFragment.evaluates_at_depthBound calleeEvaluation
        (by omega : closedSourceDataDepthBound callee ≤ budget)
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend
