import Solcore.SourceSemantics.Staging.RecursiveTrace

/-! Origin and prefix properties of the recursive staged profile. Every
propagated stage failure is backed by an actual rejected guard at the retained
source occurrence, including failures escaping a selected closure body, an ordered tuple element,
or a primitive operand.
Short-circuited operands contribute no trace and therefore cannot introduce a failure. -/

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

private def ForItemsOrigin (outcome : ForItemsOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private theorem body_result_stage {type : TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (converted : BodyResult type outcome result) {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : result = .fault (.stage originScope call reason)) : outcome = .fault (.stage originScope call reason) := by
  cases converted with
  | returned => cases failed
  | breaking => cases failed
  | continuing => cases failed
  | unit => cases failed
  | fault => exact congrArg BodyOutcome.fault (Outcome.fault.inj failed)

local macro "retain_stage_origin" : tactic =>
  `(tactic| (
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case tupleFault occurrence children ih | constructorFault occurrence children ih
      | builtinArgumentsFault occurrence children ih
      | directArgumentsFault occurrence calleeOccurrence children ih =>
      intro s c r same
      cases same
      exact ih s c r rfl
    case coercionMethod method roots selected parameters allocate body result bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case unaryMethod occurrence dispatch method operand roots selected parameters allocate body result operandIH bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case binaryMethod occurrence dispatch method first continues second roots selected parameters allocate body result firstIH secondIH bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case arm contains scrutinee hidden selected extended allocated body scrutineeIH bodyIH =>
      rename_i outcome
      cases outcome <;> simp_all [BodyOutcome.restore, BodyOrigin]
    case default contains scrutinee hidden selected body scrutineeIH bodyIH =>
      rename_i outcome
      cases outcome <;> simp_all [BodyOutcome.restore, BodyOrigin]
    case indexResult occurrence first second result ih_first ih_second =>
      cases result <;> simp_all [ExpressionOrigin]
    all_goals simp_all [ExpressionOrigin, ValuesOrigin, BodyOrigin, ForItemsOrigin]
  ))

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
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
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
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
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
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem StatementsIn.stage_origin {mode : Bool} {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : BodyOutcome}
    (trace : StatementsIn program registry mode scope context environment before statements finalContext outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : BodyOrigin outcome := by
    clear failed
    induction trace using StatementsIn.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

namespace Statements
export StatementsIn (stage_origin)
end Statements

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

theorem RawForm.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    (trace : RawForm program registry scope context environment before form requirements coercions outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using RawForm.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem CoercionStep.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionStep program registry scope context before step input outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using CoercionStep.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem CoercionPath.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionPath program registry scope context before steps input outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using CoercionPath.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

end Solcore.SourceSemantics.Staging.Recursive
