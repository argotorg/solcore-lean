import Solcore.Frontend.ClosedSourceDataDepthBound
import Solcore.Frontend.ClosedSourceDataExpression
import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.LocalScopeProperties

/- Syntax induction bounds every original data derivation directly.
No resolution, runtime typing, successful lookup or embedded-input premise is added.
Every original intermediate store and actual returned mixed value stays literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The syntax-only data bound finds every original successful derivation,
including its actual value and complete final store, at every larger budget. -/
theorem ClosedSourceDataExpression.evaluates_at_depthBound
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured
      initialStore source value finalStore)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value, finalStore) := by
  induction fragment generalizing initialStore finalStore value budget with
  | reference =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | reference named found =>
              simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
                Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
          | creation shape => cases shape
  | literal =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | wordLiteral meaning =>
              simp only [evaluateClosedSourceExpression?, interpretWordLiteral?_complete meaning,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | unit =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | unit => simp only [evaluateClosedSourceExpression?]
          | creation shape => cases shape
  | group _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | group child =>
              simpa only [evaluateClosedSourceExpression?] using ih child (by omega : _ ≤ n)
          | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | pair left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              have rightResult := rightIH right (by omega : _ ≤ n)
              simp only [evaluateClosedSourceExpression?, leftResult, rightResult,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | many _ _ headIH tailIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | many head tail =>
              have headResult := headIH head (by omega : _ ≤ n)
              have tailResult := tailIH tail (by omega : _ ≤ n)
              simp only [evaluateClosedSourceExpression?, headResult, tailResult,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | conditional _ _ _ conditionIH thenIH elseIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | conditionalTrue condition branch =>
              have conditionResult := conditionIH condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, conditionResult,
                bind, Option.bind_some, ↓reduceIte] using thenIH branch (by omega : _ ≤ n)
          | conditionalFalse condition branch =>
              have conditionResult := conditionIH condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, conditionResult, bind,
                Option.bind_some, Bool.false_eq_true, ↓reduceIte] using elseIH branch (by omega : _ ≤ n)
          | creation shape => cases shape
  | logicalNot _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | logicalNot child =>
              simp only [evaluateClosedSourceExpression?, ih child (by omega : _ ≤ n),
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | bitNot _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | bitNot child =>
              simp only [evaluateClosedSourceExpression?, ih child (by omega : _ ≤ n),
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | logicalAnd _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | andTrue left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, leftResult,
                bind, Option.bind_some, ↓reduceIte] using rightIH right (by omega : _ ≤ n)
          | andFalse left =>
              simp only [evaluateClosedSourceExpression?, leftIH left (by omega : _ ≤ n),
                bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte, pure]
          | strictWordBinary _ _ meaning => cases meaning
          | creation shape => cases shape
  | logicalOr _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | orTrue left =>
              simp only [evaluateClosedSourceExpression?, leftIH left (by omega : _ ≤ n),
                bind, Option.bind_some, ↓reduceIte, pure]
          | orFalse left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, leftResult, bind,
                Option.bind_some, Bool.false_eq_true, ↓reduceIte] using rightIH right (by omega : _ ≤ n)
          | strictWordBinary _ _ meaning => cases meaning
          | creation shape => cases shape
  | strictWordBinary _ _ notAnd notOr leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | strictWordBinary left right meaning =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              have rightResult := rightIH right (by omega : _ ≤ n)
              cases meaning <;>
                simp only [evaluateClosedSourceExpression?, leftResult, rightResult,
                  evaluateStrictWordBinary?, bind, Option.bind_some, pure]
          | andTrue _ _ => exact False.elim (notAnd rfl)
          | andFalse _ => exact False.elim (notAnd rfl)
          | orTrue _ => exact False.elim (notOr rfl)
          | orFalse _ _ => exact False.elim (notOr rfl)
          | creation shape => cases shape

end Solcore.Frontend
