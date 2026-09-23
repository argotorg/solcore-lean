import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionSafetyProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionRenaming
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionStoreProperties

/-! Exactly one canonical return statement. These wrappers add no Core
operation and do not model general early return or function invocation. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A singleton bare return yields Unit; an expression return keeps the actual
checked expression. No surrounding or unreachable statement is discarded. -/
def elaborateReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt none⟩] => some (.unit, .unit)
  | [⟨_, .returnStmt (some source)⟩] => elaborateLocalExpression? table context source
  | _ => none

inductive ReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ReturnBodyHasType table context ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      ReturnBodyHasType table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type

inductive ReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ReturnBodyEvaluates table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      ReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore

/-- Costs count the compiled expression's Core transitions, not source control
handling. Expression returns retain the child's exact cost and both stores. -/
inductive ReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ReturnBodyEvaluatesWithCost table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      ReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost

namespace LocalInputs

def checkReturnBody? (inputs : LocalInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateReturnBody? inputs.names inputs.context body

/-- Only execute the actual checked Core; present fuel exhaustion remains a
present result. Caller/store invariants are those of existing typed inputs. -/
def runReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyElaboration`
-/

/-! Exact independent preparation of a singleton-return body. The expression
rule retains resolved structure, positional lowering, and typing separately;
another Core expression of the same type is not an alternative elaboration. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolved core)
      (typing : Resolved.HasType context resolved type) :
      ReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type

theorem ReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | bare => rfl
  | expression resolution lowered typing =>
      exact elaborateLocalExpression?_complete resolution lowered typing

theorem elaborateReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type)) :
    ReturnBodyElaborates table context body core type := by
  cases elaborateReturnBody?_sound accepted with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, _⟩
      exact .bare
  | expression _ =>
      obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
      exact .expression resolution lowered typing

theorem elaborateReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateReturnBody? table context body = some (core, type) ↔
      ReturnBodyElaborates table context body core type :=
  ⟨elaborateReturnBody?_elaborates, ReturnBodyElaborates.complete⟩

theorem ReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    ReturnBodyHasType table context body type := by
  cases elaboration with
  | bare => exact .bare
  | expression resolution _ typing => exact .expression (resolution.reflects_type typing)

theorem ReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type) :
    ∃ core, ReturnBodyElaborates table context body core type := by
  obtain ⟨core, accepted⟩ := typing.elaborates
  exact ⟨core, elaborateReturnBody?_elaborates accepted⟩

/-- Exact preparation determines both Core and type, not only type agreement. -/
theorem ReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : ReturnBodyElaborates table context body leftCore leftType)
    (right : ReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyExecutionProperties`
-/

/-! Checked single-return bodies retain the child's exact Core execution.
Whole body typing stays explicit at the completed-run boundary; raw evaluation
alone cannot justify a skipped unresolved or ill-typed expression branch. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateReturnBody?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have typing := elaborateReturnBody?_sound accepted
  cases typing with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, _⟩
      constructor
      · intro evaluation; cases evaluation; exact .unit
      · intro evaluation; cases evaluation; exact .bare
  | expression _ =>
      change elaborateLocalExpression? _ _ _ = some (core, type) at accepted
      constructor
      · intro evaluation
        cases evaluation with
        | expression child => exact (elaborateLocalExpression?_evaluates_iff accepted sameIds).mp child
      · intro evaluation
        exact .expression ((elaborateLocalExpression?_evaluates_iff accepted sameIds).mpr evaluation)

/-- The wrappers add no transition: bare return executes Unit in one step,
and expression return reuses the child's path with the exact same endpoints. -/
theorem ReturnBodyEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block}
    {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) := by
  cases evaluation with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .cons .unit .refl
  | expression child => exact child.checked_toSteps accepted sameIds

theorem ReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem ReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

/-- Reflection from an actual completed run requires identity alignment but
does not require a separately typed runtime environment. -/
theorem elaborateReturnBody?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, ReturnBodyEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

namespace LocalInputs

theorem runReturnBody?_eq_some_iff {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runReturnBody? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkReturnBody? body = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Fixed-fuel completion includes whole body typing, even when a raw child
evaluation could skip unsupported syntax. Both stores and the value are exact. -/
theorem runReturnBody?_done_iff_typed_cost {inputs : LocalInputs} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runReturnBody? fuel body initialStore = some (type, .done value finalStore) ↔
      ReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ cost, ReturnBodyEvaluatesWithCost inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runReturnBody?_eq_some_iff.mp completed
    exact ⟨elaborateReturnBody?_sound checked,
      (elaborateReturnBody?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := returnBodyHasType_iff_elaborates.mp typing
    exact runReturnBody?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

/-- Typed inputs give a typed value and both exact fuel boundaries, for any
initial store. Exhaustion states are existential, not identified with each other. -/
theorem returnBody_typed_cost_execution {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ReturnBodyHasType inputs.names inputs.context body type) (store : Core.Store) :
    ∃ value cost, ReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runReturnBody? fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runReturnBody? fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := returnBodyHasType_iff_elaborates.mp typing
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates inputs.sameIds inputs.environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked inputs.sameIds
    (fuel := fuel)) (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds (fuel := fuel))
  simpa only [runReturnBody?, checkReturnBody?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

/-- Present exhaustion requires whole body typing and an independent cost
strictly above the supplied fuel. No particular suspended state is prescribed. -/
theorem runReturnBody?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runReturnBody? fuel body store = some (type, .outOfFuel suspended)) ↔
      ReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ value cost, ReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runReturnBody?_eq_some_iff.mp exhausted
    have typing := elaborateReturnBody?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ := returnBody_typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, runReturnBody?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unsupported bodies fail checking; checked bodies either complete or exhaust
their fuel. Neither path returns a machine fault, including with an arbitrary store. -/
theorem runReturnBody?_never_faults (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runReturnBody? fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runReturnBody?_eq_some_iff.mp fault
  have typing := elaborateReturnBody?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ := returnBody_typed_cost_execution typing store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyContinuationProperties`
-/

/-! Return wrappers preserve exact paths under any still-pending continuation.
The continuation is retained, not executed or discarded at the endpoint. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases evaluation with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .cons .unit .refl
  | expression child =>
      obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
      have runtimeLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
        rw [sameIds]
        exact lowered
      exact child.toStepsWithContinuation resolution runtimeLowered continuation

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyFuelBoundProperties`
-/

/-! A singleton return inherits the source bound without wrapper transitions.
The zero placeholder for unsupported body shapes is not an acceptance claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

def returnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .returnStmt none⟩] => 1
  | [⟨_, .returnStmt (some source)⟩] => localExpressionFuelBound source
  | _ => 0

theorem ReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ returnBodyFuelBound body := by
  cases evaluation with
  | bare => exact Nat.le_refl _
  | expression child => exact child.cost_le_fuelBound

theorem elaborateReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : returnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : returnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.returnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyRenamingProperties`
-/

/-! Body-level identity relabeling is independent of runtime-function entry.
Exact Core, type, rejection, and same-fuel machine results are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | bare => exact .bare
  | expression resolution lowered typing =>
      refine .expression (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

/-- Both accepted and rejected singleton checks retain the exact optional result. -/
theorem elaborateReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateReturnBody?]
      | nil =>
          rcases statement with ⟨returnSpan, payload⟩
          cases payload <;> try rfl
          case returnStmt returned =>
            cases returned with
            | none => rfl
            | some source => exact elaborateLocalExpression?_mapIds mapping injective table context source

namespace LocalInputs

theorem checkReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkReturnBody? body = inputs.checkReturnBody? body := by
  simp only [checkReturnBody?, mapIds_names, mapIds_context, elaborateReturnBody?_mapIds mapping injective]

/-- Values and exact suspended states agree at any fuel, with no acceptance premise. -/
theorem runReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runReturnBody? fuel body store = inputs.runReturnBody? fuel body store := by
  simp only [runReturnBody?, checkReturnBody?_mapIds, mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyResumptionProperties`
-/

/-! A singleton return has no additional resumption transition. Actual exhausted
states retain their pending frames and the complete original checked body. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runReturnBody?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runReturnBody? spent body store = some (type, .outOfFuel checkpoint)) (additional : Nat) :
    inputs.runReturnBody? (spent + additional) body store = some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runReturnBody?_eq_some_iff.mp exhausted
  exact runReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ReturnBodyStoreProperties`
-/

/-! Store replay preserves values and costs, while full states retain their
own stores. Completed observations and exhaustion presence are related. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : ReturnBodyEvaluates table environment replacement body value replacement := by
  cases evaluation with
  | bare => exact .bare
  | expression child => exact .expression (child.change_store replacement)

theorem ReturnBodyEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : ReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  cases evaluation with
  | bare => exact .bare
  | expression child => exact .expression (child.change_store replacement)

theorem returnBodyEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ReturnBodyEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ ReturnBodyEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem returnBodyEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        ReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runReturnBody?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runReturnBody? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runReturnBody? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runReturnBody?_done_iff_typed_cost, LocalInputs.runReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runReturnBody? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runReturnBody? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
