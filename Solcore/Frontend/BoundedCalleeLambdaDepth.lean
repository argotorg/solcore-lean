import Solcore.Frontend.ClosedSourceDataDepthBoundProperties
import Solcore.Frontend.ClosedSourceDataBodyDepthProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- A supplied successful finite callee run makes outer-call bounds compositional.
It is an explicit premise, not a search for a callee budget. The actual selected
saved fields, caller argument and intermediate/full stores are kept literally. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Compose a known successful callee budget with admitted argument and saved-body depths. -/
def boundedCalleeLambdaDepthBound (calleeBudget : Nat) (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max calleeBudget (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- A supplied finite callee run fixes its actual closure and store; argument and
body success are needed only inside the original successful whole endpoint. -/
theorem boundedCalleeLambda_evaluates_at_depthBound
    {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {initialStore calleeStore finalStore : List RuntimeValue} {calleeBudget : Nat}
    (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
      callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan,[argument]⟩⟩ = some (actual,finalStore) := by
  have independent := evaluateClosedSourceExpression?_sound selected
  unfold boundedCalleeLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic independent
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := evaluateClosedSourceExpression?_monotone (by omega : calleeBudget ≤ budget) selected
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend
