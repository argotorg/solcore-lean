import Solcore.Core.LocalFragmentInsertionPaths
import Solcore.Core.LocalFragmentInsertionProperties
import Solcore.Core.ExactFuelProperties

/-! Exact-cost insertion transports a closed final path into any outer
continuation. Only closed final paths are used to identify their lengths;
the continuation is retained, not run, and suspended states may differ. -/

set_option autoImplicit false

namespace Solcore.Core

theorem Expr.LocalFragment.steps_insert
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial expr (leading ++ suffix) initialStore)
      (State.final value finalStore)) (continuation : List Frame) :
    Steps cost
      ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix),
        continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ :=
    fragment.insertion_paths leading suffix inserted (steps_from_initial_sound path)
  have sameCost : cost = commonCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem Expr.LocalFragment.steps_reflect_insert
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value}
    (path : Steps cost
      (State.initial (expr.weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (State.final value finalStore)) (continuation : List Frame) :
    Steps cost
      ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have evaluation :=
    (fragment.evaluates_insert_iff leading suffix inserted).mp (steps_from_initial_sound path)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted evaluation
  have sameCost : cost = commonCost := (path.final_unique (paths []).2).1
  exact sameCost.symm ▸ (paths continuation).1

theorem Expr.LocalFragment.steps_insert_iff
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {cost : Nat} {initialStore finalStore : Store} {value : Value} :
    Steps cost
      (State.initial (expr.weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (State.final value finalStore) ↔
    Steps cost (State.initial expr (leading ++ suffix) initialStore)
      (State.final value finalStore) :=
  ⟨fun path => fragment.steps_reflect_insert leading suffix inserted path [],
    fun path => fragment.steps_insert leading suffix inserted path []⟩

theorem Steps.weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {cost : Nat}
    {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial expr environment initialStore) (State.final value finalStore))
    (fragment : expr.LocalFragment) (inserted : Value) (continuation : List Frame) :
    Steps cost
      ⟨.eval (expr.weakenAt 0) (inserted :: environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ :=
  fragment.steps_insert [] environment inserted path continuation

theorem Steps.reflect_weakenAt_zero_localFragment
    {expr : Expr} {environment : Environment} {inserted : Value} {cost : Nat}
    {initialStore finalStore : Store} {value : Value}
    (path : Steps cost (State.initial (expr.weakenAt 0) (inserted :: environment) initialStore)
      (State.final value finalStore))
    (fragment : expr.LocalFragment) (continuation : List Frame) :
    Steps cost
      ⟨.eval expr environment, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ :=
  fragment.steps_reflect_insert [] environment inserted path continuation

end Solcore.Core
