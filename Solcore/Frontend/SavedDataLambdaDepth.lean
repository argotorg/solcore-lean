import Solcore.Frontend.ClosedSourceDataDepthBoundProperties
import Solcore.Frontend.ClosedSourceDataBodyDepthProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Reference lookup fixes the full saved datum. This bound includes the actual
saved source body, not only caller syntax. Argument evaluation uses caller rows;
body evaluation uses freshly extended saved rows and the actual current store. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Sufficient reference-call depth given the actual saved body, not caller-only syntax. -/
def savedDataLambdaDepthBound (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max 1 (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

/-- First-match lookup and saved-body data admission bound every original full
endpoint without identifying caller and saved owners, rows, captures or stores. -/
theorem savedDataLambda_evaluates_at_depthBound
    {source argument : Syntax.Expr} {name calleeName : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
    {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
    {calleeId : Resolved.LocalId}
    (named : LocalNameTable.Lookup callerNames calleeName.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure source savedOwner savedNames savedCaptured))
    {initialStore finalStore : List RuntimeValue}
    {callSpan calleeSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan,[argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan,[argument]⟩⟩ =
        some (actual,finalStore) := by
  have picked : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨calleeSpan,.identifier calleeName⟩ (.sourceClosure source savedOwner savedNames savedCaptured)
      initialStore := .reference named found
  unfold savedDataLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee,sameStore⟩ := calleeEvaluation.deterministic picked
      cases sameCallee; cases sameStore
      obtain ⟨sameName,sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      have calleeRun : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured
          initialStore ⟨calleeSpan,.identifier calleeName⟩ =
            some (.sourceClosure source savedOwner savedNames savedCaptured,initialStore) := by
        cases budget with
        | zero => omega
        | succ budget =>
          simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
            Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure,Pure.pure]
      simpa only [evaluateClosedSourceExpression?,calleeRun,argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape,bind,Option.bind_some] using bodyRun

end Solcore.Frontend
