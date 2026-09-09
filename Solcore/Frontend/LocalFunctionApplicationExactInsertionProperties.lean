import Solcore.Frontend.LocalFunctionApplicationInsertionProperties
import Solcore.Frontend.LocalFunctionApplicationInsertionPaths
import Solcore.Core.ExactFuelProperties

/-! Supplied closed paths keep their exact cost under caller insertion.
Only final paths identify costs; outer continuations are retained, not run. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.core_steps_insert
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value}
    (path : Core.Steps cost (Core.State.initial core (leading ++ suffix) initialStore)
      (Core.State.final value finalStore)) (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix),
        continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := elaboration.core_insertion_paths leading suffix inserted
    (Core.steps_from_initial_sound path)
  have sameCost : cost = commonCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem LocalFunctionApplicationElaborates.core_steps_reflect_insert
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value}
    (path : Core.Steps cost
      (Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix)
        initialStore) (Core.State.final value finalStore)) (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have evaluation := (elaboration.core_evaluates_insert_iff leading suffix inserted).mp
    (Core.steps_from_initial_sound path)
  obtain ⟨commonCost, paths⟩ :=
    elaboration.core_insertion_paths leading suffix inserted evaluation
  have sameCost : cost = commonCost := (path.final_unique (paths []).2).1
  exact sameCost.symm ▸ (paths continuation).1

theorem LocalFunctionApplicationElaborates.core_steps_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Steps cost
      (Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix)
        initialStore) (Core.State.final value finalStore) ↔
    Core.Steps cost (Core.State.initial core (leading ++ suffix) initialStore)
      (Core.State.final value finalStore) :=
  ⟨fun path => elaboration.core_steps_reflect_insert leading suffix inserted path [],
    fun path => elaboration.core_steps_insert leading suffix inserted path []⟩

end Solcore.Frontend
