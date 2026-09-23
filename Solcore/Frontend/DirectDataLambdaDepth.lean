import Solcore.Frontend.ClosedSource

/- A direct unary lambda creates its saved datum at depth one. The bound applies
only with the independent lambda shape and data argument/body gates. Captured
fields and actual intermediate/final stores remain literal, without typing. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A source-only sufficient depth for direct unary application, not saved calls. -/
def directDataLambdaDepthBound (argument : Syntax.Expr) (body : Syntax.Block) : Nat :=
  max 1 (max (closedSourceDataDepthBound argument) (closedSourceDataBodyDepthBound body)) + 1

private theorem creation_at_positive_depth
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    {budget : Nat} (positive : 0 < budget) :
    evaluateClosedSourceExpression? budget owner names captured store source =
      some (.sourceClosure source owner names captured, store) := by
  cases budget with
  | zero => omega
  | succ budget =>
      cases shape <;> simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
        bind, Option.bind_some, pure, Pure.pure]

/-- Every original direct application endpoint is found at the computable upper
depth under arbitrary caller rows, mixed values and complete actual stores. -/
theorem directDataLambda_evaluates_at_depthBound
    {source argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : SourceUnaryLambdaShape source name body)
    (argumentFragment : ClosedSourceDataExpression argument)
    (bodyFragment : ClosedSourceDataBody body)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {actual : RuntimeValue}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore)
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) := by
  have created : ClosedSourceExpressionEvaluates owner names captured initialStore
      source (.sourceClosure source owner names captured) initialStore := .creation shape
  unfold directDataLambdaDepthBound at enough
  cases budget with
  | zero => omega
  | succ budget =>
    cases original with
    | creation impossible => cases impossible
    | call actualShape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨sameCallee, sameStore⟩ := calleeEvaluation.deterministic created
      cases sameCallee; cases sameStore
      obtain ⟨sameName, sameBody⟩ := Prod.mk.inj (Option.some.inj
        ((sourceUnaryLambdaShape?_iff.mpr actualShape).symm.trans
          (sourceUnaryLambdaShape?_iff.mpr shape)))
      cases sameName; cases sameBody
      have calleeRun := creation_at_positive_depth shape owner names captured initialStore
        (by omega : 0 < budget)
      have argumentRun := argumentFragment.evaluates_at_depthBound argumentEvaluation
        (by omega : closedSourceDataDepthBound argument ≤ budget)
      have bodyRun := bodyFragment.evaluates_at_depthBound bodyEvaluation
        (by omega : closedSourceDataBodyDepthBound body ≤ budget)
      simpa only [evaluateClosedSourceExpression?, calleeRun, argumentRun,
        sourceUnaryLambdaShape?_iff.mpr shape, bind, Option.bind_some] using bodyRun

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.DirectDataLambdaDepthDecisionProperties`
-/

/- Exact finite decisions for direct unary syntax with separate data gates.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source argument : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {owner : Resolved.DeclarationId} {names : LocalNameTable}
variable {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
variable {callSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment

/-- A sufficiently deep direct call returns exactly each original full endpoint. -/
theorem directDataLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem directDataLambda_evaluate_depth_stable
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem directDataLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : directDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have found := directDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment original enough
    rw [absent] at found
    cases found
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One syntax-bounded search decides whether any budget can return a successful
endpoint for this direct application, not for arbitrary saved callees. -/
theorem directDataLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (directDataLambdaDepthBound argument body)
      owner names captured initialStore ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (directDataLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget owner names captured initialStore
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
