import Solcore.Frontend.ClosedSourceConditionalProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Original conditional boundaries consume independent judgments and direct
computations separately. No typing, failure classification or cost claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedSourceConditionalBoundaries

/-- A previously evaluated actual Bool fixes the original selected child and store. -/
theorem fixed_guard_selects_exact_original_branch
    {owner names captured initialStore middleStore finalStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {span question colon thenBranch elseBranch value} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore ↔
    ClosedSourceExpressionEvaluates owner names captured middleStore
      (if choice then thenBranch else elseBranch) value finalStore := by
  constructor
  · intro evaluated
    obtain ⟨other, otherStore, otherGuard, selected⟩ :=
      closedSourceExpressionEvaluates_conditional_iff.mp evaluated
    obtain ⟨same, rfl⟩ := guard.deterministic otherGuard
    cases same
    exact selected
  · intro selected
    exact closedSourceExpressionEvaluates_conditional_iff.mpr
      ⟨choice, middleStore, guard, selected⟩

/-- Original marker spans and unselected syntax need no evaluation premise. -/
theorem changing_only_unselected_branch_preserves_endpoint
    {owner names captured initialStore middleStore finalStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {span question colon selected ignored replacement value} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question
        (if choice then selected else ignored) colon (if choice then ignored else selected)⟩
      value finalStore ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question
        (if choice then selected else replacement) colon (if choice then replacement else selected)⟩
      value finalStore := by
  rw [fixed_guard_selects_exact_original_branch guard,
    fixed_guard_selects_exact_original_branch guard]
  cases choice <;> rfl

/-- An actual non-Bool guard cannot be reinterpreted from source spelling. -/
theorem actual_non_boolean_guard_has_no_derivation
    {owner names captured initialStore middleStore condition actual}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition actual middleStore)
    (notBool : ∀ choice, actual ≠ RuntimeValue.bool choice)
    {span question colon thenBranch elseBranch value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore := by
  intro evaluated
  obtain ⟨choice, _, otherGuard, _⟩ :=
    closedSourceExpressionEvaluates_conditional_iff.mp evaluated
  exact notBool choice (guard.deterministic otherGuard).1

/-- All-depth absence for a known non-Bool is not a general None classifier. -/
theorem actual_non_boolean_guard_has_no_success_at_any_depth
    {owner names captured initialStore middleStore condition actual}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition actual middleStore)
    (notBool : ∀ choice, actual ≠ RuntimeValue.bool choice)
    (budget : Nat) (span question colon : Syntax.SourceSpan)
    (thenBranch elseBranch : Syntax.Expr) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ = none := by
  cases computed : evaluateClosedSourceExpression? budget owner names captured initialStore
    ⟨span, .conditional condition question thenBranch colon elseBranch⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim (actual_non_boolean_guard_has_no_derivation guard notBool
        (evaluateClosedSourceExpression?_sound computed))

/-- Direct depth computations are paired with an independent original derivation. -/
theorem direct_unit_choice_has_exact_depth_two
    {owner names captured store id choice} {name : Syntax.Identifier}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (RuntimeValue.bool choice))
    (span question colon guardSpan unitSpan tupleSpan : Syntax.SourceSpan)
    (ignored : Syntax.Expr) :
    let unitSource : Syntax.Expr := ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩
    let source : Syntax.Expr := ⟨span, .conditional ⟨guardSpan, .identifier name⟩ question
      (if choice then unitSource else ignored) colon (if choice then ignored else unitSource)⟩
    ClosedSourceExpressionEvaluates owner names captured store source .unit store ∧
      evaluateClosedSourceExpression? 0 owner names captured store source = none ∧
      evaluateClosedSourceExpression? 1 owner names captured store source = none ∧
      evaluateClosedSourceExpression? 2 owner names captured store source = some (.unit, store) := by
  dsimp only
  have guard : ClosedSourceExpressionEvaluates owner names captured store
      ⟨guardSpan, .identifier name⟩ (.bool choice) store := .reference named found
  constructor
  · apply (fixed_guard_selects_exact_original_branch guard).mpr
    cases choice <;> exact .unit
  · cases choice <;>
      simp only [evaluateClosedSourceExpression?_conditional,
        evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some,
        Option.bind_none, pure, Bool.false_eq_true, ↓reduceIte, and_self]

/-- Selecting creation preserves the original source and all actual captured rows. -/
theorem selected_source_creation_keeps_every_saved_field
    {owner names captured initialStore middleStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {source name body} (shape : SourceUnaryLambdaShape source name body)
    (span question colon : Syntax.SourceSpan) (ignored : Syntax.Expr) :
    let conditional : Syntax.Expr := ⟨span, .conditional condition question
      (if choice then source else ignored) colon (if choice then ignored else source)⟩
    ClosedSourceExpressionEvaluates owner names captured initialStore conditional
        (.sourceClosure source owner names captured) middleStore ∧
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget owner names captured initialStore conditional =
          some (.sourceClosure source owner names captured, middleStore) := by
  dsimp only
  have selected : ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question (if choice then source else ignored) colon
        (if choice then ignored else source)⟩
      (.sourceClosure source owner names captured) middleStore := by
    apply (fixed_guard_selects_exact_original_branch guard).mpr
    cases choice <;> exact .creation shape
  exact ⟨selected, evaluateClosedSourceExpression?_eventually_complete selected⟩

end Tests.ClosedSourceConditionalBoundaries
