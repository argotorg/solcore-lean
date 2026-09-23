import Solcore.Frontend.ClosedSource

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

/-!
## Consolidated module: `Solcore.Frontend.BoundedCalleeLambdaDepthDecisionProperties`
-/

/- Exact outer-call decisions under a supplied successful finite callee run.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source callee argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue}
variable {initialStore calleeStore : List RuntimeValue} {calleeBudget : Nat}
variable (selected : evaluateClosedSourceExpression? calleeBudget callerOwner callerNames callerCaptured initialStore
  callee = some (.sourceClosure source savedOwner savedNames savedCaptured,calleeStore))
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment selected

/-- A sufficiently deep bounded-selected-callee call returns exactly each original full endpoint. -/
theorem boundedCalleeLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem boundedCalleeLambda_evaluate_depth_stable
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem boundedCalleeLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : boundedCalleeLambdaDepthBound calleeBudget argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := boundedCalleeLambda_evaluates_at_depthBound shape argumentFragment bodyFragment selected original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- A supplied callee run and actual saved syntax bound one outer-call search.
This does not find a successful callee budget or decide arbitrary callee evaluation. -/
theorem boundedCalleeLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (boundedCalleeLambdaDepthBound calleeBudget argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (boundedCalleeLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment selected
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
