import Solcore.Frontend.ClosedSourceEvaluation

/- Exact original-body and unary-call correspondence, with no child callback
hypothesis or old-value image restriction. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem body_forward {owner names captured initialStore body value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore body value finalStore) :
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names captured
      initialStore body value finalStore := by
  induction evaluated using ClosedSourceBodyEvaluates.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True) with
  | reference => trivial
  | unit => trivial
  | wordLiteral => trivial
  | group => trivial
  | pair => trivial
  | many => trivial
  | creation => trivial
  | call => trivial
  | conditionalTrue => trivial
  | conditionalFalse => trivial
  | bare => exact .bare
  | expression child _ => exact .expression child
  | block _ ih => exact .block ih
  | binding initializer _ _ ih => exact .binding initializer ih
  | inferred initializer _ _ ih => exact .inferred initializer ih
  | discard expression _ _ ih => exact .discard expression ih
  | ifTrue condition _ _ ih => exact .ifTrue condition ih
  | ifFalse condition _ _ ih => exact .ifFalse condition ih
  | wordMatch scrutinee choice _ _ ih => exact .wordMatch scrutinee choice ih

/-- Exact original-body correspondence at every actual mixed input and endpoint. -/
theorem closedSourceBodyEvaluates_iff {owner names captured initialStore body value finalStore} :
    ClosedSourceBodyEvaluates owner names captured initialStore body value finalStore ↔
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names captured
      initialStore body value finalStore := by
  constructor
  · exact body_forward
  · intro evaluated
    induction evaluated with
    | bare => exact .bare
    | expression child => exact .expression child
    | block _ ih => exact .block ih
    | binding initializer _ ih => exact .binding initializer ih
    | inferred initializer _ ih => exact .inferred initializer ih
    | discard expression _ ih => exact .discard expression ih
    | ifTrue condition _ ih => exact .ifTrue condition ih
    | ifFalse condition _ ih => exact .ifFalse condition ih
    | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee choice ih

/-- Exact compatibility only for original unary calls, retaining caller children,
saved lexical fields and actual intermediate stores without callback premises. -/
theorem closedSourceExpressionEvaluates_call_iff
    {owner names captured initialStore finalStore span argumentsSpan callee argument result} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore ↔
    SourceLambdaEvaluates ClosedSourceExpressionEvaluates
      (SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates) owner names captured
      initialStore ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact .call shape calleeEvaluation argumentEvaluation
          (closedSourceBodyEvaluates_iff.mp bodyEvaluation)
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact .call shape calleeEvaluation argumentEvaluation
          (closedSourceBodyEvaluates_iff.mpr bodyEvaluation)

end Solcore.Frontend
