import Solcore.Frontend.SavedDataLambdaDepth
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties

/- Exact finite decisions for lookup-known saved unary syntax with separate data gates.
No successful argument or body premise is required for these decision laws. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source argument : Syntax.Expr} {name calleeName : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (argumentFragment : ClosedSourceDataExpression argument)
variable (bodyFragment : ClosedSourceDataBody body)
variable {callerOwner savedOwner : Resolved.DeclarationId} {callerNames savedNames : LocalNameTable}
variable {callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue} {calleeId : Resolved.LocalId}
variable (named : LocalNameTable.Lookup callerNames calleeName.value calleeId)
variable (found : Resolved.LocalScope.Lookup callerCaptured calleeId
  (.sourceClosure source savedOwner savedNames savedCaptured))
variable {initialStore : List RuntimeValue}
variable {callSpan calleeSpan argumentsSpan : Syntax.SourceSpan}
include shape argumentFragment bodyFragment named found

/-- A sufficiently deep lookup-known saved call returns exactly each original full endpoint. -/
theorem savedDataLambda_evaluate_at_depthBound_iff
    {actual : RuntimeValue} {finalStore : List RuntimeValue} {budget : Nat}
    (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = some (actual, finalStore) ↔
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ actual finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,
    fun original => savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found original enough⟩

/-- Whole Option stability includes argument and selected-body failure. -/
theorem savedDataLambda_evaluate_depth_stable
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ =
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ := by
  cases low : evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
  | none =>
    cases high : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      have atBound := savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found
        (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
      rw [low] at atBound
      cases atBound
  | some endpoint =>
    obtain ⟨actual, finalStore⟩ := endpoint
    exact evaluateClosedSourceExpression?_monotone enough low

/-- Sufficient-depth None excludes every original successful call endpoint,
without classifying its cause or assuming empty lexical inputs. -/
theorem savedDataLambda_evaluate_depth_none_iff
    {budget : Nat} (enough : savedDataLambdaDepthBound argument body ≤ budget) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ actual finalStore, ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ actual finalStore := by
  constructor
  · intro absent actual finalStore original
    have accepted := savedDataLambda_evaluates_at_depthBound shape argumentFragment bodyFragment named found original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))

/-- One search bounded by the actual saved syntax decides whether any budget has a successful
endpoint for this lookup-known saved application, not for arbitrary callees. -/
theorem savedDataLambda_evaluate_depth_none_iff_all_budgets :
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound argument body)
      callerOwner callerNames callerCaptured initialStore ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none ↔
    ∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ = none := by
  constructor
  · intro absent budget
    have impossible := (savedDataLambda_evaluate_depth_none_iff shape argumentFragment bodyFragment named found
      (Nat.le_refl _)).mp absent
    cases ran : evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured initialStore
        ⟨callSpan, .call ⟨calleeSpan,.identifier calleeName⟩ ⟨argumentsSpan, [argument]⟩⟩ with
    | none => rfl
    | some endpoint =>
      obtain ⟨actual, finalStore⟩ := endpoint
      exact False.elim (impossible actual finalStore (evaluateClosedSourceExpression?_sound ran))
  · intro absent
    exact absent _

end
end Solcore.Frontend
