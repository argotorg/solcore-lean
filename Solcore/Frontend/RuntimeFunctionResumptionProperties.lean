import Solcore.Frontend.TerminalReturnBodyResumptionProperties
import Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties

/-! Complete entry checkpoints resume their actual Core state. Exact source
costs retain whole preparation, and compiled paths retain compilation provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem runRuntimeFunction?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : runRuntimeFunction? types owner declaration arguments spent store =
      some (type, .outOfFuel checkpoint)) (additional : Nat) :
    runRuntimeFunction? types owner declaration arguments (spent + additional) store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp exhausted
  exact runRuntimeFunction?_eq_some_iff.mpr
    ⟨prepared, preparation, sameType, (Core.runStateful_resume execution additional).symm⟩

theorem RuntimeFunctionEvaluatesWithCost.residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost spent : Nat} {checkpoint : Core.State}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (exhausted : runRuntimeFunction? types owner declaration arguments spent initialStore =
      some (type, .outOfFuel checkpoint)) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have execution : Core.runStateful spent (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) initialStore) = .outOfFuel checkpoint := by
        simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
          Option.some.injEq, Prod.mk.injEq, true_and] using exhausted
      exact bodyCost.checked_residual_of_outOfFuel preparation.body.complete prepared.inputs.sameIds execution

theorem RuntimeFunctionEvaluatesWithCost.compiled_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost spent : Nat} {checkpoint : Core.State}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (exhausted : Core.runStateful spent (Core.State.initial compiled.core
      (arguments.reverse.map (·.value)) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.compiled_toSteps compilation).residual_of_outOfFuel exhausted

end Solcore.Frontend
