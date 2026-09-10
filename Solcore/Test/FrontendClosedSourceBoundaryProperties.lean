import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Boundary consumers for the callback-free syntax fragment.
Successful store invariance is not termination or a fault classifier. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedSourceBoundaries

theorem expression_success_keeps_the_actual_store
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction evaluated using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun _ _ _ initialStore _ _ finalStore _ => finalStore = initialStore) with
  | reference _ _ => rfl
  | unit => rfl
  | wordLiteral _ => rfl
  | group _ ih => exact ih
  | pair _ _ leftIH rightIH => exact rightIH.trans leftIH
  | many _ _ headIH tailIH => exact tailIH.trans headIH
  | creation _ => rfl
  | call _ _ _ _ calleeIH argumentIH bodyIH =>
      exact bodyIH.trans (argumentIH.trans calleeIH)
  | conditionalTrue _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | conditionalFalse _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | bare => rfl
  | expression _ ih => exact ih
  | block _ ih => exact ih
  | binding _ _ initializerIH tailIH => exact tailIH.trans initializerIH
  | inferred _ _ initializerIH tailIH => exact tailIH.trans initializerIH
  | discard _ _ expressionIH tailIH => exact tailIH.trans expressionIH
  | ifTrue _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | ifFalse _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | wordMatch _ _ _ scrutineeIH branchIH => exact branchIH.trans scrutineeIH

theorem body_success_keeps_the_actual_store
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  have original := closedSourceBodyEvaluates_iff.mp evaluated
  clear evaluated
  induction original with
  | bare => rfl
  | expression child => exact expression_success_keeps_the_actual_store child
  | block _ ih => exact ih
  | binding child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | inferred child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | discard child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | ifTrue child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | ifFalse child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | wordMatch child _ _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)

theorem manual_singleton_tuple_has_no_success
    {owner names captured initialStore span tupleSpan child value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .tuple ⟨tupleSpan, [child]⟩⟩ value finalStore := by
  intro evaluated
  cases evaluated with
  | creation shape => cases shape

theorem a_non_source_callee_has_no_unary_call
    {owner names captured initialStore callee calleeValue calleeStore}
    (calleeEvaluation : ClosedSourceExpressionEvaluates owner names captured initialStore
      callee calleeValue calleeStore)
    (notSource : ∀ source savedOwner savedNames savedCaptured,
      calleeValue ≠ RuntimeValue.sourceClosure source savedOwner savedNames savedCaptured)
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ value finalStore := by
  intro evaluated
  obtain ⟨_, _, _, _, _, _, _, _, _, _, otherCallee, _, _⟩ :=
    SourceLambdaEvaluates.call_iff.mp (closedSourceExpressionEvaluates_call_iff.mp evaluated)
  exact notSource _ _ _ _ (calleeEvaluation.deterministic otherCallee).1

theorem arbitrary_core_closures_are_inert_call_targets
    {owner names captured initialStore referenceSpan name id parameterType resultType code captures}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id
      (RuntimeValue.coreClosure parameterType resultType code captures))
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call ⟨referenceSpan, .identifier name⟩ ⟨argumentsSpan, [argument]⟩⟩ value finalStore :=
  a_non_source_callee_has_no_unary_call (.reference named found)
    (by intro source savedOwner savedNames savedCaptured impossible; cases impossible)

theorem arbitrary_host_functions_are_inert_call_targets
    {owner names captured initialStore referenceSpan name id host}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (RuntimeValue.hostFunction host))
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call ⟨referenceSpan, .identifier name⟩ ⟨argumentsSpan, [argument]⟩⟩ value finalStore :=
  a_non_source_callee_has_no_unary_call (.reference named found)
    (by intro source savedOwner savedNames savedCaptured impossible; cases impossible)

theorem creation_with_empty_body_does_not_execute_it
    {owner names captured store source name bodySpan}
    (shape : SourceUnaryLambdaShape source name ⟨bodySpan, []⟩)
    {span argumentsSpan argument value finalStore} :
    ClosedSourceExpressionEvaluates owner names captured store source
        (.sourceClosure source owner names captured) store ∧
      ¬ ClosedSourceExpressionEvaluates owner names captured store
        ⟨span, .call source ⟨argumentsSpan, [argument]⟩⟩ value finalStore := by
  constructor
  · exact .creation shape
  · intro evaluated
    obtain ⟨_, _, _, _, _, _, _, _, _, otherShape, otherCallee, _, otherBody⟩ :=
      SourceLambdaEvaluates.call_iff.mp (closedSourceExpressionEvaluates_call_iff.mp evaluated)
    obtain ⟨sameCallee, sameStore⟩ :=
      ClosedSourceExpressionEvaluates.deterministic (.creation shape) otherCallee
    cases sameCallee
    cases sameStore
    have sameShape := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr shape).symm.trans
        (sourceUnaryLambdaShape?_iff.mpr otherShape)))
    obtain ⟨rfl, rfl⟩ := sameShape
    cases otherBody

theorem zero_and_multiple_arguments_have_no_success
    {owner names captured store span argumentsSpan callee first second rest value finalStore} :
    (¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .call callee ⟨argumentsSpan, []⟩⟩ value finalStore) ∧
    (¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .call callee ⟨argumentsSpan, first :: second :: rest⟩⟩ value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape

end Tests.ClosedSourceBoundaries
