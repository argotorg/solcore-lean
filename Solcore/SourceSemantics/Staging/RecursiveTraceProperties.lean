import Solcore.SourceSemantics.Staging.RecursiveTrace

/-! Origin and prefix properties of the recursive staged profile. Every
propagated stage failure is backed by an actual rejected guard at the retained
source occurrence, including failures escaping a selected closure body. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

def Generated (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault) : Prop :=
  ∃ callee arguments metadata value,
    Occurrence scope call (.call callee arguments (.indirect metadata)) ∧
    CallBoundary.GuardRejects scope.guards call arguments value reason

private def ExpressionOrigin (outcome : Outcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private def ValuesOrigin (outcome : ValuesOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private def BodyOrigin (outcome : BodyOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private theorem body_result_stage {type : TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (converted : BodyResult type outcome result) {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : result = .fault (.stage originScope call reason)) : outcome = .fault (.stage originScope call reason) := by
  cases converted with
  | returned => cases failed
  | unit => cases failed
  | fault => exact congrArg BodyOutcome.fault (Outcome.fault.inj failed)

theorem Expression.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry scope context environment before id outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using Expression.rec
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    all_goals intro s c r same
    all_goals cases same
    all_goals dsimp only [ExpressionOrigin, ValuesOrigin, BodyOrigin] at *
    all_goals solve_by_elim
  exact origin originScope call reason failed

theorem Expressions.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Expressions program registry scope context environment before ids outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ValuesOrigin outcome := by
    clear failed
    induction trace using Expressions.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    all_goals intro s c r same
    all_goals cases same
    all_goals dsimp only [ExpressionOrigin, ValuesOrigin, BodyOrigin] at *
    all_goals solve_by_elim
  exact origin originScope call reason failed

theorem Applies.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {value : Value} {values : List Value} {outcome : Outcome}
    (trace : Applies program registry scope context before value values outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using Applies.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    all_goals intro s c r same
    all_goals cases same
    all_goals dsimp only [ExpressionOrigin, ValuesOrigin, BodyOrigin] at *
    all_goals solve_by_elim
  exact origin originScope call reason failed

theorem Statements.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : BodyOutcome}
    (trace : Statements program registry scope context environment before statements finalContext outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : BodyOrigin outcome := by
    clear failed
    induction trace using Statements.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    all_goals intro s c r same
    all_goals cases same
    all_goals dsimp only [ExpressionOrigin, ValuesOrigin, BodyOrigin] at *
    all_goals solve_by_elim
  exact origin originScope call reason failed

/-- Successful argument traversal retains source arity without a separate
assumption about a runtime argument evaluator. -/
theorem Expressions.length {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {values : List Value}
    (trace : Expressions program registry scope context environment before ids (.values values) after) :
    ids.length = values.length := by
  induction ids generalizing before values with
  | nil => cases trace; rfl
  | cons head rest ih =>
    cases trace with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

/-- The body scope is the selected closure scope. The caller's return marker,
source table and cumulative local substitution are not substituted for it. -/
theorem Applies.closure_scope {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {function : Closure} {values : List Value} {outcome : Outcome}
    (trace : Applies program registry scope context before (.closure function) values outcome after)
    (arity : function.parameters.length = values.length) :
    ∃ child, registry.Closure function child ∧ child.source = function.source ∧
      child.context = function.context ∧ child.evidence = function.evidence := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _ _ _ _ _ =>
    exact ⟨_, selected, registry.source selected, registry.context selected, registry.evidence selected⟩

end Solcore.SourceSemantics.Staging.Recursive
