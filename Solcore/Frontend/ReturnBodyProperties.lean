import Solcore.Frontend.ReturnBody
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionSafetyProperties
import Solcore.Frontend.LocalExpressionCostProperties

/-! Exact singleton-body checking and independent value/store/cost laws.
Raw evaluation laws require neither whole-body typing nor resolution. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type) :
    ∃ core, elaborateReturnBody? table context body = some (core, type) := by
  cases typing with
  | bare => exact ⟨.unit, rfl⟩
  | expression child => exact localExpressionHasType_iff_elaborates.mp child

theorem elaborateReturnBody?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type)) :
    ReturnBodyHasType table context body type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => simp only [elaborateReturnBody?, reduceCtorEq] at accepted
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateReturnBody?, reduceCtorEq] at accepted
      | nil =>
          rcases statement with ⟨returnSpan, payload⟩
          cases payload <;> simp only [elaborateReturnBody?, reduceCtorEq] at accepted
          case returnStmt returned =>
            cases returned with
            | none =>
                simp only [Option.some.injEq, Prod.mk.injEq] at accepted
                rcases accepted with ⟨rfl, rfl⟩
                exact .bare
            | some source =>
                exact .expression (localExpressionHasType_iff_elaborates.mpr ⟨core, accepted⟩)

theorem returnBodyHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} : ReturnBodyHasType table context body type ↔
      ∃ core, elaborateReturnBody? table context body = some (core, type) :=
  ⟨ReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateReturnBody?_sound accepted⟩

theorem elaborateReturnBody?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaborateReturnBody?_sound accepted with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, _⟩
      exact .unit
  | expression child => exact elaborateLocalExpression?_core_hasType accepted

theorem ReturnBodyHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : ReturnBodyHasType table context body left)
    (second : ReturnBodyHasType table context body right) : left = right := by
  cases first with
  | bare => cases second; rfl
  | expression child =>
      cases second with
      | expression other => exact child.type_unique other

theorem elaborateReturnBody?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateReturnBody? table context body = none ↔
      ¬ ∃ type, ReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateReturnBody?_sound result⟩)

/-- Wrapper ranges do not change either form of singleton return checking. -/
theorem elaborateReturnBody?_spans (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan otherBlockSpan otherReturnSpan : Syntax.SourceSpan) :
    elaborateReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? table context ⟨otherBlockSpan, [⟨otherReturnSpan, .returnStmt returned⟩]⟩ := by
  cases returned <;> rfl

theorem ReturnBodyEvaluates.store_eq {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  cases evaluation with
  | bare => rfl
  | expression child => exact child.store_eq

theorem ReturnBodyEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : ReturnBodyEvaluates table environment initialStore body left leftStore)
    (second : ReturnBodyEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first with
  | bare => cases second; exact ⟨rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact child.deterministic other

theorem ReturnBodyHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) (store : Core.Store) :
    ∃ value, ReturnBodyEvaluates table environment store body value store ∧
      Core.ValueHasType value type := by
  cases typing with
  | bare => exact ⟨.unit, .bare, .unit⟩
  | expression child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .expression evaluation, typed⟩

theorem ReturnBodyEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {type : Core.Ty} {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore)
    (typing : ReturnBodyHasType table context body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, storeEq⟩ := evaluation.deterministic evaluated
  exact ⟨typed, storeEq⟩

theorem ReturnBodyEvaluatesWithCost.erase {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    ReturnBodyEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | bare => exact .bare
  | expression child => exact .expression child.erase

theorem ReturnBodyEvaluates.exists_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore) :
    ∃ cost, ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | bare => exact ⟨1, .bare⟩
  | expression child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .expression costed⟩

theorem returnBodyEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} :
    ReturnBodyEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨ReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem ReturnBodyEvaluatesWithCost.store_eq {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem ReturnBodyEvaluatesWithCost.cost_pos {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | bare => exact Nat.zero_lt_succ _
  | expression child => exact child.cost_pos

theorem ReturnBodyEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : ReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : ReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases first with
  | bare => cases second; exact ⟨rfl, rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact child.deterministic other

end Solcore.Frontend
