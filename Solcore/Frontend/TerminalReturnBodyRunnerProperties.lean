import Solcore.Frontend.TerminalReturnBodyExecutionProperties

/-! Whole checking and actual typed inputs characterize completed and exhausted
terminal-body runs. Raw skipped-arm success cannot bypass checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace LocalInputs

/-- Embedding preserves every optional result, including checker failure and
the complete suspended state at any fuel. -/
theorem runTerminalReturnBody?_single (inputs : LocalInputs) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := rfl

theorem runTerminalReturnBody?_conditional (inputs : LocalInputs) (fuel : Nat)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store =
      inputs.runConditionalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store := rfl

theorem runTerminalReturnBody?_eq_some_iff {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runTerminalReturnBody? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkTerminalReturnBody? body = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runTerminalReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Fixed-fuel completion includes whole body typing, even when a raw child
evaluation could skip unsupported syntax. Both stores and the value are exact. -/
theorem runTerminalReturnBody?_done_iff_typed_cost {inputs : LocalInputs} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTerminalReturnBody? fuel body initialStore = some (type, .done value finalStore) ↔
      TerminalReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ cost, TerminalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runTerminalReturnBody?_eq_some_iff.mp completed
    exact ⟨elaborateTerminalReturnBody?_sound checked,
      (elaborateTerminalReturnBody?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := terminalReturnBodyHasType_iff_elaborates.mp typing
    exact runTerminalReturnBody?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

/-- Typed inputs give a typed value and both exact fuel boundaries, for any
initial store. Exhaustion states are existential, not identified with each other. -/
theorem terminalReturnBody_typed_cost_execution {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnBodyHasType inputs.names inputs.context body type) (store : Core.Store) :
    ∃ value cost, TerminalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runTerminalReturnBody? fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runTerminalReturnBody? fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := terminalReturnBodyHasType_iff_elaborates.mp typing
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates inputs.sameIds inputs.environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked inputs.sameIds
    (fuel := fuel)) (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds (fuel := fuel))
  simpa only [runTerminalReturnBody?, checkTerminalReturnBody?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

/-- Present exhaustion requires whole body typing and an independent cost
strictly above the supplied fuel. No particular suspended state is prescribed. -/
theorem runTerminalReturnBody?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runTerminalReturnBody? fuel body store = some (type, .outOfFuel suspended)) ↔
      TerminalReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ value cost, TerminalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runTerminalReturnBody?_eq_some_iff.mp exhausted
    have typing := elaborateTerminalReturnBody?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ := terminalReturnBody_typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, runTerminalReturnBody?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unsupported bodies fail checking; checked bodies either complete or exhaust
their fuel. Neither path returns a machine fault, including with an arbitrary store. -/
theorem runTerminalReturnBody?_never_faults (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runTerminalReturnBody? fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runTerminalReturnBody?_eq_some_iff.mp fault
  have typing := elaborateTerminalReturnBody?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ := terminalReturnBody_typed_cost_execution typing store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end LocalInputs
end Solcore.Frontend
