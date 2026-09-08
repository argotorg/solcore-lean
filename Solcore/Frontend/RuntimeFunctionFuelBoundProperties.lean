import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties

/-! Source-derived fuel suffices uniformly over matching actual typed arguments.
Compilation provenance and whole entry typing remain mandatory. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionEvaluatesWithCost.cost_le_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) : cost ≤ terminalReturnBodyFuelBound declaration.value.body := by
  cases evaluation with
  | intro _ body => exact body.cost_le_fuelBound

theorem RuntimeFunctionHasType.run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty}
    (typing : RuntimeFunctionHasType types owner declaration arguments type)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? types owner declaration arguments fuel store =
      some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := typing.typed_cost_execution store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

/-- One source-computable bound applies to every matching actual argument list;
no value for an uninhabited declared type is manufactured. -/
theorem RuntimeFunctionCompiles.run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value compiled.returnType ∧
      runRuntimeFunction? types owner declaration arguments fuel store = some (compiled.returnType, .done value store) ∧
      Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
        .done value store := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    compilation.typed_compiled_execution arguments matchingTypes store
  have bounded := Nat.le_trans costed.cost_le_fuelBound enough
  exact ⟨value, valueTyped, costed.run_done_iff.mpr bounded, (boundaries fuel).1.mpr bounded⟩

end Solcore.Frontend
