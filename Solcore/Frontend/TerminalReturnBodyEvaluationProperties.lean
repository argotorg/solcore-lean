import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.TerminalReturnBodyEvaluation

/-! The disjoint source shapes retain each original value/store/cost judgment.
Typed existence uses the actual aligned environment, not representative values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnBodyEvaluates.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  cases evaluation with
  | single child => exact child.store_eq
  | conditional child => exact child.store_eq

theorem TerminalReturnBodyEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TerminalReturnBodyEvaluates table environment initialStore body left leftStore)
    (second : TerminalReturnBodyEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | conditional other => cases child <;> cases other
  | conditional child =>
      cases second with
      | single other => cases other <;> cases child
      | conditional other => exact child.deterministic other

theorem TerminalReturnBodyHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) (store : Core.Store) :
    ∃ value, TerminalReturnBodyEvaluates table environment store body value store ∧
      Core.ValueHasType value type := by
  cases typing with
  | single child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .single evaluation, typed⟩
  | conditional child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .conditional evaluation, typed⟩

theorem TerminalReturnBodyEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty} {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore)
    (typing : TerminalReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TerminalReturnBodyEvaluatesWithCost.erase
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnBodyEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | single child => exact .single child.erase
  | conditional child => exact .conditional child.erase

theorem TerminalReturnBodyEvaluates.exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore) :
    ∃ cost, TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | single child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .single costed⟩
  | conditional child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .conditional costed⟩

theorem terminalReturnBodyEvaluates_iff_exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TerminalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨TerminalReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TerminalReturnBodyEvaluatesWithCost.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TerminalReturnBodyEvaluatesWithCost.cost_pos
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | single child => exact child.cost_pos
  | conditional child => exact child.cost_pos

theorem TerminalReturnBodyEvaluatesWithCost.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TerminalReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : TerminalReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases first with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | conditional other => cases child <;> cases other
  | conditional child =>
      cases second with
      | single other => cases other <;> cases child
      | conditional other => exact child.deterministic other

end Solcore.Frontend
