import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.ClosedSourceEvaluationCompatibility
import Solcore.Frontend.SourceLambdaEvaluationProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.LocalScopeProperties

/- Every finite derivation is found at all sufficiently large depths. The bound
depends on the derivation, not source size; no termination or step-cost claim. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem eventually_step {P : Nat → Prop} (threshold : Nat)
    (step : ∀ n, threshold ≤ n → P (n + 1)) :
    ∃ required, ∀ budget, required ≤ budget → P budget := by
  refine ⟨threshold + 1, ?_⟩
  intro budget large
  cases budget with
  | zero => omega
  | succ n => exact step n (by omega)

/-- Every finite expression derivation is found at all sufficiently large depths. -/
theorem evaluateClosedSourceExpression?_eventually_complete
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceExpression? budget owner names captured initialStore source = some (value, finalStore) := by
  induction evaluated using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value finalStore _ =>
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore)) with
  | reference named found =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
  | unit =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?]
  | wordLiteral meaning =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?, interpretWordLiteral?_complete meaning,
        bind, Option.bind_some, pure]
  | group _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceExpression?] using ih n large
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      obtain ⟨r, rightIH⟩ := rightIH
      apply eventually_step (max l r)
      intro n large
      have left := leftIH n (by omega)
      have right := rightIH n (by omega)
      simp only [evaluateClosedSourceExpression?, left, right, bind, Option.bind_some, pure]
  | creation shape =>
      cases shape <;> apply eventually_step 0 <;> intro n _ <;>
        simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_some, pure]
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
      obtain ⟨f, calleeIH⟩ := calleeIH
      obtain ⟨a, argumentIH⟩ := argumentIH
      obtain ⟨b, bodyIH⟩ := bodyIH
      apply eventually_step (max f (max a b))
      intro n large
      have callee := calleeIH n (by omega)
      have argument := argumentIH n (by omega)
      have body := bodyIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, callee, argument,
        sourceUnaryLambdaShape?_iff.mpr shape, bind, Option.bind_some] using body
  | conditionalTrue _ _ conditionIH branchIH | conditionalFalse _ _ conditionIH branchIH =>
      obtain ⟨c, conditionIH⟩ := conditionIH
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max c b)
      intro n large
      have condition := conditionIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, condition, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte] using branch
  | logicalNot _ ih | bitNot _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simp only [evaluateClosedSourceExpression?, ih n large, bind, Option.bind_some, pure]
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      obtain ⟨r, rightIH⟩ := rightIH
      apply eventually_step (max l r)
      intro n large
      have left := leftIH n (by omega)
      have right := rightIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, left, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte] using right
  | andFalse _ leftIH | orTrue _ leftIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      apply eventually_step l
      intro n large
      simp only [evaluateClosedSourceExpression?, leftIH n large, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte, pure]
  | bare =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceBody?]
  | expression _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | block _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | binding _ _ initializerIH tailIH | inferred _ _ initializerIH tailIH
  | discard _ _ initializerIH tailIH | ifTrue _ _ initializerIH tailIH | ifFalse _ _ initializerIH tailIH =>
      obtain ⟨i, initializerIH⟩ := initializerIH
      obtain ⟨t, tailIH⟩ := tailIH
      apply eventually_step (max i t)
      intro n large
      have initializer := initializerIH n (by omega)
      have tail := tailIH n (by omega)
      simpa only [evaluateClosedSourceBody?, initializer, bind, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte] using tail
  | wordMatch _ choice _ scrutineeIH branchIH =>
      obtain ⟨s, scrutineeIH⟩ := scrutineeIH
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max s b)
      intro n large
      have scrutinee := scrutineeIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceBody?, scrutinee, chooseRuntimeWordMatch?_iff.mpr choice,
        bind, Option.bind_some] using branch

/-- Every finite body derivation is found at all sufficiently large depths. -/
theorem evaluateClosedSourceBody?_eventually_complete
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceBody? budget owner names captured initialStore source = some (value, finalStore) := by
  have original := closedSourceBodyEvaluates_iff.mp evaluated
  clear evaluated
  induction original with
  | bare =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceBody?]
  | expression child =>
      obtain ⟨k, child⟩ := evaluateClosedSourceExpression?_eventually_complete child
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using child n large
  | block _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | binding initializer _ tailIH | inferred initializer _ tailIH
  | discard initializer _ tailIH | ifTrue initializer _ tailIH | ifFalse initializer _ tailIH =>
      obtain ⟨i, initializerIH⟩ := evaluateClosedSourceExpression?_eventually_complete initializer
      obtain ⟨t, tailIH⟩ := tailIH
      apply eventually_step (max i t)
      intro n large
      have head := initializerIH n (by omega)
      have tail := tailIH n (by omega)
      simpa only [evaluateClosedSourceBody?, head, bind, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte] using tail
  | wordMatch scrutinee choice _ branchIH =>
      obtain ⟨s, scrutineeIH⟩ := evaluateClosedSourceExpression?_eventually_complete scrutinee
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max s b)
      intro n large
      have scrutinee := scrutineeIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceBody?, scrutinee, chooseRuntimeWordMatch?_iff.mpr choice,
        bind, Option.bind_some] using branch

end Solcore.Frontend
