import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TerminalReturnTreeEvaluation

/-! Recursive raw laws need no whole checking. Typed existence separately uses
the actual aligned and typed environment; unchanged stores require neither. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | single child => exact child.store_eq
  | ifTrue condition _ ih | ifFalse condition _ ih => exact ih.trans condition.store_eq

theorem TerminalReturnTreeEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TerminalReturnTreeEvaluates table environment initialStore body left leftStore)
    (second : TerminalReturnTreeEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | ifTrue _ _ | ifFalse _ _ => cases child
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch

theorem TerminalReturnTreeHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) (store : Core.Store) :
    ∃ value, TerminalReturnTreeEvaluates table environment store body value store ∧
      Core.ValueHasType value type := by
  induction typing with
  | single child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .single evaluation, typed⟩
  | conditional conditionTyped _ _ thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionType⟩ :=
        conditionTyped.evaluates sameIds environmentTyped store
      obtain ⟨choice, rfl⟩ := conditionType.bool_shape
      cases choice with
      | false =>
          obtain ⟨value, evaluation, typed⟩ := elseIH
          exact ⟨value, .ifFalse conditionEvaluation evaluation, typed⟩
      | true =>
          obtain ⟨value, evaluation, typed⟩ := thenIH
          exact ⟨value, .ifTrue conditionEvaluation evaluation, typed⟩

theorem TerminalReturnTreeEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty} {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (typing : TerminalReturnTreeHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TerminalReturnTreeEvaluatesWithCost.erase
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := by
  induction evaluation with
  | single child => exact .single child.erase
  | ifTrue condition _ ih => exact .ifTrue condition.erase ih
  | ifFalse condition _ ih => exact .ifFalse condition.erase ih

theorem TerminalReturnTreeEvaluates.exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore) :
    ∃ cost, TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := by
  induction evaluation with
  | single child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .single costed⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue conditionCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse conditionCost branchCost⟩

theorem terminalReturnTreeEvaluates_iff_exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨TerminalReturnTreeEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TerminalReturnTreeEvaluatesWithCost.store_eq
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TerminalReturnTreeEvaluatesWithCost.cost_pos
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | single child => exact child.cost_pos
  | ifTrue _ _ | ifFalse _ _ => omega

theorem TerminalReturnTreeEvaluatesWithCost.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TerminalReturnTreeEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : TerminalReturnTreeEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | ifTrue _ _ | ifFalse _ _ => cases child
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ =>
          have impossible := (condition.deterministic otherCondition).1
          cases impossible
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
