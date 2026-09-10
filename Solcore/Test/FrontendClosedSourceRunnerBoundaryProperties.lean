import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

set_option autoImplicit false
namespace Tests.ClosedSourceRunnerBoundaries
open Solcore Solcore.Frontend

theorem an_expression_witness_exists_exactly_for_a_finite_derivation
    {owner names captured store source value finalStore} :
    (∃ budget, evaluateClosedSourceExpression? budget owner names captured store source =
      some (value, finalStore)) ↔
    ClosedSourceExpressionEvaluates owner names captured store source value finalStore := by
  constructor
  · rintro ⟨budget, accepted⟩
    exact evaluateClosedSourceExpression?_sound accepted
  · intro evaluated
    obtain ⟨required, found⟩ := evaluateClosedSourceExpression?_eventually_complete evaluated
    exact ⟨required, found required (Nat.le_refl _)⟩

theorem a_body_witness_exists_exactly_for_a_finite_derivation
    {owner names captured store source value finalStore} :
    (∃ budget, evaluateClosedSourceBody? budget owner names captured store source =
      some (value, finalStore)) ↔
    ClosedSourceBodyEvaluates owner names captured store source value finalStore := by
  constructor
  · rintro ⟨budget, accepted⟩
    exact evaluateClosedSourceBody?_sound accepted
  · intro evaluated
    obtain ⟨required, found⟩ := evaluateClosedSourceBody?_eventually_complete evaluated
    exact ⟨required, found required (Nat.le_refl _)⟩

theorem successful_expression_budgets_cannot_change_actual_endpoints
    {firstBudget secondBudget owner names captured store source first firstStore second secondStore}
    (left : evaluateClosedSourceExpression? firstBudget owner names captured store source =
      some (first, firstStore))
    (right : evaluateClosedSourceExpression? secondBudget owner names captured store source =
      some (second, secondStore)) : first = second ∧ firstStore = secondStore :=
  (evaluateClosedSourceExpression?_sound left).deterministic
    (evaluateClosedSourceExpression?_sound right)

theorem successful_body_budgets_cannot_change_actual_endpoints
    {firstBudget secondBudget owner names captured store source first firstStore second secondStore}
    (left : evaluateClosedSourceBody? firstBudget owner names captured store source =
      some (first, firstStore))
    (right : evaluateClosedSourceBody? secondBudget owner names captured store source =
      some (second, secondStore)) : first = second ∧ firstStore = secondStore :=
  (evaluateClosedSourceBody?_sound left).deterministic
    (evaluateClosedSourceBody?_sound right)

theorem zero_depth_none_does_not_rule_out_an_independent_success
    {owner names captured store span tupleSpan} :
    evaluateClosedSourceExpression? 0 owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ = none ∧
    ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ .unit store ∧
    evaluateClosedSourceExpression? 1 owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ = some (.unit, store) := by
  exact ⟨by simp only [evaluateClosedSourceExpression?], .unit,
    by simp only [evaluateClosedSourceExpression?]⟩

private def selfCall (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .call ⟨span, .identifier name⟩ ⟨span, [⟨span, .identifier name⟩]⟩⟩
private def loopBody (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span, [⟨span, .returnStmt (some (selfCall span name))⟩]⟩
private def loopLambda (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred name⟩]⟩ none (loopBody span name)⟩
private def omegaSource (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .call (loopLambda span name) ⟨span, [loopLambda span name]⟩⟩

private theorem loopBody_none (budget : Nat) {owner names captured store span name} :
    evaluateClosedSourceBody? budget owner
      ((name.value, Resolved.freshLocalId owner (names.map Prod.snd)) :: names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),
        .sourceClosure (loopLambda span name) owner names captured) :: captured)
      store (loopBody span name) = none := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ n =>
          cases n with
          | zero => simp only [loopBody, evaluateClosedSourceBody?, evaluateClosedSourceExpression?]
          | succ k =>
              cases k with
              | zero => simp only [loopBody, evaluateClosedSourceBody?, selfCall,
                  evaluateClosedSourceExpression?, bind, Option.bind_none]
              | succ l =>
                  have smaller := ih (l + 1) (by omega)
                  simpa only [loopBody, evaluateClosedSourceBody?, selfCall,
                    evaluateClosedSourceExpression?, loopLambda, sourceUnaryLambdaShape?,
                    LocalNameTable.lookup?, Resolved.LocalScope.lookup?, ↓reduceIte,
                    bind, Option.bind_some, pure] using smaller

theorem original_self_application_has_no_success_at_any_depth
    (budget : Nat) {owner names captured store span name} :
    evaluateClosedSourceExpression? budget owner names captured store
      (omegaSource span name) = none := by
  cases budget with
  | zero => simp only [evaluateClosedSourceExpression?]
  | succ n =>
      cases n with
      | zero => simp only [omegaSource, evaluateClosedSourceExpression?, bind, Option.bind_none]
      | succ k =>
          have body := loopBody_none (k + 1) (owner := owner) (names := names)
            (captured := captured) (store := store) (span := span) (name := name)
          simpa only [omegaSource, loopLambda, evaluateClosedSourceExpression?,
            sourceUnaryLambdaShape?, bind, Option.bind_some, pure] using body

theorem original_self_application_has_no_finite_successful_derivation
    {owner names captured store span name value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured store
      (omegaSource span name) value finalStore := by
  intro evaluated
  obtain ⟨budget, found⟩ :=
    an_expression_witness_exists_exactly_for_a_finite_derivation.mpr evaluated
  rw [original_self_application_has_no_success_at_any_depth budget] at found
  cases found

end Tests.ClosedSourceRunnerBoundaries
