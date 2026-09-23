import Solcore.Frontend.ClosedSource

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

/-!
## Consolidated module: `Solcore.Frontend.DataCalleeLambdaDepthDecisionProperties`
-/

/- Exact finite decisions under an independently successful data-callee selection.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (calleeFragment : ClosedSourceDataExpression callee)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore : List RuntimeValue}
variable (selected : ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
  callee (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape calleeFragment argumentFragment bodyFragment selected

/-- A sufficiently deep independently selected data-callee call returns exactly each original full endpoint. -/
theorem dataCalleeLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem dataCalleeLambda_evaluate_depth_stable
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem dataCalleeLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : dataCalleeLambdaDepthBound callee argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := dataCalleeLambda_evaluates_at_depthBound shape calleeFragment argumentFragment bodyFragment selected original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One search bounded by the actual saved syntax decides whether any budget has a successful
endpoint for this independently selected data-callee application, not for arbitrary callees. -/
theorem dataCalleeLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (dataCalleeLambdaDepthBound callee argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (dataCalleeLambda_evaluate_depth_none_iff shape calleeFragment argumentFragment bodyFragment selected
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
