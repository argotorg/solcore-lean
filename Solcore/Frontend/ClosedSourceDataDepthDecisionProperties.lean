import Solcore.Frontend.ClosedSourceDataDepthBoundProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties

/- Exact finite search on the independently admitted data-expression syntax.
No lookup, literal validity or runtime typing premise guarantees success.
All absence claims concern this existing successful-evaluation judgment only. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- At every sufficient source depth, the actual result and entire final store
agree exactly with the original judgment over arbitrary mixed runtime inputs. -/
theorem ClosedSourceDataExpression.evaluate_at_depthBound_iff
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {value : RuntimeValue} {budget : Nat}
    (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value,finalStore) ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,fun original => fragment.evaluates_at_depthBound original enough⟩

/-- Whole Option stability includes semantic failure, not only successful values.
The bound is sufficient; a selected short-circuit path may need much less depth. -/
theorem ClosedSourceDataExpression.evaluate_depth_stable
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
        owner names captured initialStore source := by
  cases low : evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
      owner names captured initialStore source with
  | none =>
      cases high : evaluateClosedSourceExpression? budget owner names captured initialStore source with
      | none => rfl
      | some endpoint =>
          obtain ⟨value,finalStore⟩ := endpoint
          have atBound := fragment.evaluates_at_depthBound
            (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
          rw [low] at atBound
          cases atBound
  | some endpoint =>
      obtain ⟨value,finalStore⟩ := endpoint
      exact evaluateClosedSourceExpression?_monotone enough low

/-- Failure at a sufficient depth excludes every original successful endpoint.
It does not classify missing values, wrong payloads or invalid literal spellings. -/
theorem ClosedSourceDataExpression.evaluate_depth_none_iff
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source = none ↔
      ∀ value finalStore, ¬ ClosedSourceExpressionEvaluates owner names captured
        initialStore source value finalStore := by
  constructor
  · intro absent value finalStore original
    have accepted := fragment.evaluates_at_depthBound original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases actual : evaluateClosedSourceExpression? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceExpression?_sound actual))

/-- A single sufficient search decides whether any budget could succeed on this
gated syntax; no analogous conclusion is claimed for arbitrary source calls. -/
theorem ClosedSourceDataExpression.evaluate_depth_none_iff_all_budgets
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue) :
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
        owner names captured initialStore source = none ↔
      ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore source = none := by
  constructor
  · intro absent budget
    have impossible := (fragment.evaluate_depth_none_iff owner names captured initialStore (Nat.le_refl _)).mp absent
    cases actual : evaluateClosedSourceExpression? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceExpression?_sound actual))
  · intro absent
    exact absent _

end Solcore.Frontend
