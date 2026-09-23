import Solcore.Frontend.ClosedSource

/- Original conditionals retain independent marker ranges at every depth.
The constructor proof and full runner calculation are independent inductions. -/
set_option autoImplicit false
namespace Tests.ClosedSourceConditionalDepth
open Solcore Solcore.Frontend

private def tower (outer question colon guard : Nat → Syntax.SourceSpan)
    (leaf : Syntax.SourceSpan) (gate : Syntax.Identifier) :
    Nat → Syntax.Identifier → Syntax.Identifier → Syntax.Expr
  | 0, left, _ => ⟨leaf, .identifier left⟩
  | n + 1, left, right =>
      ⟨outer n, .conditional ⟨guard n, .identifier gate⟩ (question n)
        (tower outer question colon guard leaf gate n left right) (colon n)
        (tower outer question colon guard leaf gate n right left)⟩

private def selected (choice : Bool) : Nat → RuntimeValue → RuntimeValue → RuntimeValue
  | 0, left, _ => left
  | n + 1, left, right =>
      if choice then selected choice n left right else selected choice n right left

variable (outer question colon guard : Nat → Syntax.SourceSpan) (leaf : Syntax.SourceSpan)
  (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
  (gate left right : Syntax.Identifier) (gateId leftId rightId : Resolved.LocalId)
  (choice : Bool) (leftValue rightValue : RuntimeValue)
  (gateNamed : LocalNameTable.Lookup names gate.value gateId)
  (gateFound : Resolved.LocalScope.Lookup captured gateId (.bool choice))
  (leftNamed : LocalNameTable.Lookup names left.value leftId)
  (leftFound : Resolved.LocalScope.Lookup captured leftId leftValue)
  (rightNamed : LocalNameTable.Lookup names right.value rightId)
  (rightFound : Resolved.LocalScope.Lookup captured rightId rightValue)

include gateNamed gateFound leftNamed leftFound rightNamed rightFound

private theorem original (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (tower outer question colon guard leaf gate n left right)
      (selected choice n leftValue rightValue) store := by
  induction n generalizing left right leftId rightId leftValue rightValue with
  | zero => exact .reference leftNamed leftFound
  | succ n ih =>
      cases choice
      · exact .conditionalFalse (.reference gateNamed gateFound)
          (ih right left rightId leftId rightValue leftValue
            rightNamed rightFound leftNamed leftFound)
      · exact .conditionalTrue (.reference gateNamed gateFound)
          (ih left right leftId rightId leftValue rightValue
            leftNamed leftFound rightNamed rightFound)

theorem original_endpoint_and_eventual_discovery (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
        (tower outer question colon guard leaf gate n left right)
        (selected choice n leftValue rightValue) store ∧
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget owner names captured store
          (tower outer question colon guard leaf gate n left right) =
          some (selected choice n leftValue rightValue, store) := by
  have evaluated := original outer question colon guard leaf owner names captured store
    gate left right gateId leftId rightId choice leftValue rightValue
    gateNamed gateFound leftNamed leftFound rightNamed rightFound n
  exact ⟨evaluated, evaluateClosedSourceExpression?_eventually_complete evaluated⟩

omit gateNamed gateFound leftNamed leftFound rightNamed rightFound in
private theorem reference_run {name : Syntax.Identifier} {id : Resolved.LocalId}
    {value : RuntimeValue} (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (span : Syntax.SourceSpan)
    (budget : Nat) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured store
      ⟨span, .identifier name⟩ = some (value, store) := by
  simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]

theorem exact_outcome_at_every_budget (n budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      (tower outer question colon guard leaf gate n left right) =
      if n + 1 ≤ budget then some (selected choice n leftValue rightValue, store) else none := by
  induction n generalizing left right leftId rightId leftValue rightValue budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simpa only [tower, selected, Nat.succ_eq_add_one, Nat.le_add_left,
            ↓reduceIte] using reference_run owner names captured store leftNamed leftFound leaf budget
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero => simp [tower, evaluateClosedSourceExpression?, bind, Option.bind_none]
          | succ budget =>
              simp only [tower, evaluateClosedSourceExpression?_conditional,
                reference_run owner names captured store gateNamed gateFound,
                bind, Option.bind_some]
              cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, selected]
              · rw [ih right left rightId leftId rightValue leftValue
                  rightNamed rightFound leftNamed leftFound]
                simp only [Nat.succ_le_succ_iff]
              · rw [ih left right leftId rightId leftValue rightValue
                  leftNamed leftFound rightNamed rightFound]
                simp only [Nat.succ_le_succ_iff]

theorem direct_threshold_result_supplies_soundness (n : Nat) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
        (tower outer question colon guard leaf gate n left right) =
        some (selected choice n leftValue rightValue, store) ∧
      ClosedSourceExpressionEvaluates owner names captured store
        (tower outer question colon guard leaf gate n left right)
        (selected choice n leftValue rightValue) store := by
  have result := exact_outcome_at_every_budget outer question colon guard leaf owner names
    captured store gate left right gateId leftId rightId choice leftValue rightValue
    gateNamed gateFound leftNamed leftFound rightNamed rightFound n (n + 1)
  simp only [Nat.le_refl, ↓reduceIte] at result
  exact ⟨result, evaluateClosedSourceExpression?_sound result⟩

omit gateFound leftFound rightFound in
theorem same_original_source_in_both_boolean_environments
    (environments : Bool → Resolved.LocalScope RuntimeValue)
    (guards : ∀ b, Resolved.LocalScope.Lookup (environments b) gateId (.bool b))
    (lefts : ∀ b, Resolved.LocalScope.Lookup (environments b) leftId leftValue)
    (rights : ∀ b, Resolved.LocalScope.Lookup (environments b) rightId rightValue)
    (n : Nat) :
    ∀ b, ClosedSourceExpressionEvaluates owner names (environments b) store
        (tower outer question colon guard leaf gate n left right)
        (selected b n leftValue rightValue) store ∧
      ∀ budget, evaluateClosedSourceExpression? budget owner names (environments b) store
        (tower outer question colon guard leaf gate n left right) =
        if n + 1 ≤ budget then some (selected b n leftValue rightValue, store) else none := by
  intro b
  exact ⟨original outer question colon guard leaf owner names (environments b) store
    gate left right gateId leftId rightId b leftValue rightValue
    gateNamed (guards b) leftNamed (lefts b) rightNamed (rights b) n,
    exact_outcome_at_every_budget outer question colon guard leaf owner names (environments b)
      store gate left right gateId leftId rightId b leftValue rightValue
      gateNamed (guards b) leftNamed (lefts b) rightNamed (rights b) n⟩

end Tests.ClosedSourceConditionalDepth
