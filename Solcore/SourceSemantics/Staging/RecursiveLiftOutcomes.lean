import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! Results of lifting an ordinary execution into recursive staged semantics.
Ordinary results retain their exact heap. A stage rejection retains the heap
reached by its genuine staged trace, before the rejected call's arguments. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.Lifting
open Frontend Frontend.SourceInference

def embed (outcome : Dynamic.ExpressionOutcome) : Outcome :=
  match outcome with
  | .value value => .value value
  | .fault reason => .fault (.semantic reason)

/-- A rejection can stop before the ordinary trace's endpoint. Its trace,
rather than an unrelated heap condition, records the actual reached prefix. -/
inductive Adapted (plain : Dynamic.ExpressionOutcome) (plainAfter : Dynamic.Heap) :
    Outcome → Dynamic.Heap → Prop where
  | completed : Adapted plain plainAfter (embed plain) plainAfter
  | rejected (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault)
      (reached : Dynamic.Heap) :
      Adapted plain plainAfter (.fault (.stage scope call reason)) reached

def ExpressionLift (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (id : ExpressionId) (plain : Dynamic.ExpressionOutcome) (plainAfter : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Expression program registry scope context environment before id staged reached ∧
    Adapted plain plainAfter staged reached

def ApplicationLift (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (before : Dynamic.Heap) (function : Dynamic.Value)
    (arguments : List Dynamic.Value) (plain : Dynamic.ExpressionOutcome)
    (plainAfter : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Applies program registry scope context before function arguments staged reached ∧
    Adapted plain plainAfter staged reached

theorem ExpressionLift.completed {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (trace : Expression program registry scope context environment before id (embed plain) after) :
    ExpressionLift program registry scope context environment before id plain after :=
  ⟨_, _, trace, .completed⟩

theorem ExpressionLift.rejected {program : Program} {registry : Registry} {scope origin : Scope}
    {context : Context} {environment : Dynamic.Environment} {before reached after : Dynamic.Heap}
    {id call : ExpressionId} {reason : CallGuard.Fault} {plain : Dynamic.ExpressionOutcome}
    (trace : Expression program registry scope context environment before id
      (.fault (.stage origin call reason)) reached) :
    ExpressionLift program registry scope context environment before id plain after :=
  ⟨_, _, trace, .rejected origin call reason reached⟩

/-- Successful and semantic-fault results match the ordinary trace exactly;
the only other result is an authenticated stage rejection. -/
theorem ExpressionLift.cases {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (lifted : ExpressionLift program registry scope context environment before id plain after) :
    Expression program registry scope context environment before id (embed plain) after ∨
      ∃ origin call reason reached,
        Expression program registry scope context environment before id
          (.fault (.stage origin call reason)) reached ∧ Generated origin call reason := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  cases adapted with
  | completed => exact .inl trace
  | rejected origin call reason reached =>
    exact .inr ⟨origin, call, reason, reached, trace, trace.stage_origin rfl⟩

theorem ExpressionLift.sized {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (lifted : ExpressionLift program registry scope context environment before id plain after) :
    ∃ size staged reached,
      Size.Expression program registry size scope context environment before id staged reached ∧
      Adapted plain after staged reached := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  obtain ⟨size, measured⟩ := Size.Expression.of_trace trace
  exact ⟨size, staged, reached, measured, adapted⟩

theorem ApplicationLift.cases {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Dynamic.Heap} {function : Dynamic.Value}
    {arguments : List Dynamic.Value} {plain : Dynamic.ExpressionOutcome}
    (lifted : ApplicationLift program registry scope context before function arguments plain after) :
    Applies program registry scope context before function arguments (embed plain) after ∨
      ∃ origin call reason reached,
        Applies program registry scope context before function arguments
          (.fault (.stage origin call reason)) reached ∧ Generated origin call reason := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  cases adapted with
  | completed => exact .inl trace
  | rejected origin call reason reached =>
    exact .inr ⟨origin, call, reason, reached, trace, trace.stage_origin rfl⟩

theorem ApplicationLift.sized {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Dynamic.Heap} {function : Dynamic.Value}
    {arguments : List Dynamic.Value} {plain : Dynamic.ExpressionOutcome}
    (lifted : ApplicationLift program registry scope context before function arguments plain after) :
    ∃ size staged reached,
      Size.Applies program registry size scope context before function arguments staged reached ∧
      Adapted plain after staged reached := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  obtain ⟨size, measured⟩ := Size.Applies.of_trace trace
  exact ⟨size, staged, reached, measured, adapted⟩

end Solcore.SourceSemantics.Staging.Recursive.Lifting
