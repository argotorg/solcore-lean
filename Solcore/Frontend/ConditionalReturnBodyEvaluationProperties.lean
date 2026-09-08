import Solcore.Frontend.ConditionalReturnBody
import Solcore.Frontend.ConditionalReturnBodyEvaluation

/-! Raw terminal-conditional laws retain exact stores without requiring whole
acceptance. Typed existence uses actual aligned, typed runtime inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyEvaluates.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  cases evaluation with
  | ifTrue condition branch | ifFalse condition branch => exact branch.store_eq.trans condition.store_eq

theorem ConditionalReturnBodyEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : ConditionalReturnBodyEvaluates table environment initialStore body left leftStore)
    (second : ConditionalReturnBodyEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first with
  | ifTrue condition branch =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact branch.deterministic otherBranch
      | ifFalse otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
  | ifFalse condition branch =>
      cases second with
      | ifTrue otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact branch.deterministic otherBranch

theorem ConditionalReturnBodyHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ConditionalReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) (store : Core.Store) :
    ∃ value, ConditionalReturnBodyEvaluates table environment store body value store ∧
      Core.ValueHasType value type := by
  cases typing with
  | intro conditionTyped thenTyped elseTyped =>
      obtain ⟨conditionValue, conditionEvaluation, conditionType⟩ :=
        conditionTyped.evaluates sameIds environmentTyped store
      obtain ⟨choice, rfl⟩ := conditionType.bool_shape
      cases choice with
      | false =>
          obtain ⟨value, evaluation, typed⟩ := elseTyped.evaluates sameIds environmentTyped store
          exact ⟨value, .ifFalse conditionEvaluation evaluation, typed⟩
      | true =>
          obtain ⟨value, evaluation, typed⟩ := thenTyped.evaluates sameIds environmentTyped store
          exact ⟨value, .ifTrue conditionEvaluation evaluation, typed⟩

theorem ConditionalReturnBodyEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty} {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore)
    (typing : ConditionalReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem ConditionalReturnBodyEvaluatesWithCost.erase
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    ConditionalReturnBodyEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue condition.erase branch.erase
  | ifFalse condition branch => exact .ifFalse condition.erase branch.erase

theorem ConditionalReturnBodyEvaluates.exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
    ∃ cost, ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | ifTrue condition branch =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := branch.exists_cost
      exact ⟨_, .ifTrue conditionCost branchCost⟩
  | ifFalse condition branch =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := branch.exists_cost
      exact ⟨_, .ifFalse conditionCost branchCost⟩

theorem conditionalReturnBodyEvaluates_iff_exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ConditionalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨ConditionalReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem ConditionalReturnBodyEvaluatesWithCost.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem ConditionalReturnBodyEvaluatesWithCost.cost_pos
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation <;> omega

theorem ConditionalReturnBodyEvaluatesWithCost.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases first with
  | ifTrue condition branch =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branch.deterministic otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
  | ifFalse condition branch =>
      cases second with
      | ifTrue otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branch.deterministic otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
