import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Core.FuelResumptionProperties

/-!
# Return bodies

Single returns, terminal `if`, and return trees.
-/

section
-- leanmerge: from Solcore.Frontend.ReturnBody
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
end

section
-- leanmerge: from Solcore.Frontend.ConditionalReturnBody
/-! A separate, nonrecursive adapter for one terminal if/else statement.
Both arms use the existing singleton-return adapter under the original inputs.
This does not extend function compilation or implement general early returns. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Retain the exact condition and both checked arms; neither an absent else
nor surrounding statements are discarded. -/
def elaborateConditionalReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .ifThen condition thenBody (some elseBody)⟩] => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? table context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateReturnBody? table context thenBody
        let (elseCore, elseType) ← elaborateReturnBody? table context elseBody
        if thenType = elseType then
          return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none

inductive ConditionalReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | intro {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType table context condition .bool)
      (thenTyping : ReturnBodyHasType table context thenBody type)
      (elseTyping : ReturnBodyHasType table context elseBody type) :
      ConditionalReturnBodyHasType table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Exact elaboration is independent of the executable checker and retains
condition resolution, positional lowering, and both original arm elaborations. -/
inductive ConditionalReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | intro {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionResolution : ResolvesLocalExpression table condition conditionResolved)
      (conditionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) conditionResolved conditionCore)
      (conditionTyping : Resolved.HasType context conditionResolved .bool)
      (thenElaboration : ReturnBodyElaborates table context thenBody thenCore type)
      (elseElaboration : ReturnBodyElaborates table context elseBody elseCore type) :
      ConditionalReturnBodyElaborates table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

namespace LocalInputs

def checkConditionalReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateConditionalReturnBody? inputs.names inputs.context body

/-- Execute only the actual checked Core using the actual ordered values.
Exhaustion remains a present result with its original suspended state. -/
def runConditionalReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkConditionalReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyEvaluation`
-/

/-! Independent selected-arm semantics for a terminal conditional statement.
An unselected arm need not evaluate; whole checking is a separate judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ConditionalReturnBodyEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : ReturnBodyEvaluates table environment middleStore thenBody value finalStore) :
      ConditionalReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : ReturnBodyEvaluates table environment middleStore elseBody value finalStore) :
      ConditionalReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Costs include condition evaluation, the selected arm and the two Core
conditional transitions. Bare return arms retain their one Unit transition. -/
inductive ConditionalReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : ReturnBodyEvaluatesWithCost table environment
        middleStore thenBody value finalStore branchCost) :
      ConditionalReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : ReturnBodyEvaluatesWithCost table environment
        middleStore elseBody value finalStore branchCost) :
      ConditionalReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyEvaluationProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyProperties`
-/

/-! Independent typing and exact elaboration characterize the separate terminal
conditional checker. Both original return arms remain mandatory premises. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateConditionalReturnBody?_children
    {table : LocalNameTable} {context : Resolved.Context}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? table context condition = some (conditionCore, .bool) ∧
      elaborateReturnBody? table context thenBody = some (thenCore, type) ∧
      elaborateReturnBody? table context elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  simp only [elaborateConditionalReturnBody?, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

theorem ConditionalReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateConditionalReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      simp [elaborateConditionalReturnBody?,
        elaborateLocalExpression?_complete resolution lowered typing, thenArm.complete, elseArm.complete]

theorem elaborateConditionalReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    ConditionalReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
      | nil =>
          rcases statement with ⟨ifSpan, payload⟩
          cases payload <;> try simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => simp only [reduceCtorEq] at accepted
            | some elseBody =>
                obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                  thenAccepted, elseAccepted, rfl⟩ :=
                  elaborateConditionalReturnBody?_children (blockSpan := blockSpan) (ifSpan := ifSpan) accepted
                obtain ⟨resolved, resolution, lowered, typing⟩ :=
                  elaborateLocalExpression?_sound conditionAccepted
                exact .intro resolution lowered typing
                  (elaborateReturnBody?_elaborates thenAccepted) (elaborateReturnBody?_elaborates elseAccepted)

theorem elaborateConditionalReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateConditionalReturnBody? table context body = some (core, type) ↔
      ConditionalReturnBodyElaborates table context body core type :=
  ⟨elaborateConditionalReturnBody?_elaborates, ConditionalReturnBodyElaborates.complete⟩

theorem ConditionalReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    ConditionalReturnBodyHasType table context body type := by
  cases elaboration with
  | intro resolution _ typing thenArm elseArm =>
      exact .intro (resolution.reflects_type typing) thenArm.hasType elseArm.hasType

theorem ConditionalReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    ∃ core, ConditionalReturnBodyElaborates table context body core type := by
  cases typing with
  | intro conditionTyping thenTyping elseTyping =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenArm⟩ := thenTyping.elaborates_exact
      obtain ⟨elseCore, elseArm⟩ := elseTyping.elaborates_exact
      exact ⟨.ifE conditionCore thenCore elseCore, .intro resolution lowered typed thenArm elseArm⟩

theorem ConditionalReturnBodyHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    ∃ core, elaborateConditionalReturnBody? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateConditionalReturnBody?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    ConditionalReturnBodyHasType table context body type :=
  (elaborateConditionalReturnBody?_elaborates accepted).hasType

theorem conditionalReturnBodyHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} : ConditionalReturnBodyHasType table context body type ↔
      ∃ core, elaborateConditionalReturnBody? table context body = some (core, type) :=
  ⟨ConditionalReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateConditionalReturnBody?_sound accepted⟩

theorem elaborateConditionalReturnBody?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro _ lowered typing thenArm elseArm =>
      exact .ifE (lowered.preserves_type typing)
        (elaborateReturnBody?_core_hasType thenArm.complete) (elaborateReturnBody?_core_hasType elseArm.complete)

theorem ConditionalReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : ConditionalReturnBodyElaborates table context body leftCore leftType)
    (right : ConditionalReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem ConditionalReturnBodyHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : ConditionalReturnBodyHasType table context body left)
    (second : ConditionalReturnBodyHasType table context body right) : left = right := by
  cases first with
  | intro _ thenTyping _ =>
      cases second with
      | intro _ otherTyping _ => exact thenTyping.type_unique otherTyping

theorem elaborateConditionalReturnBody?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateConditionalReturnBody? table context body = none ↔
      ¬ ∃ type, ConditionalReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateConditionalReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateConditionalReturnBody?_sound result⟩)

/-- Only the enclosing block and conditional-statement ranges change; the
original condition and both original arm trees are retained. -/
theorem elaborateConditionalReturnBody?_spans (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan otherBlockSpan otherIfSpan : Syntax.SourceSpan) :
    elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨otherBlockSpan, [⟨otherIfSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := rfl

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyExecutionProperties`
-/

/-! Exact checked simulation for terminal conditionals. Whole elaboration keeps
both arms; raw reflection needs identity alignment but no typed environment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateConditionalReturnBody?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ConditionalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro resolution lowered typing thenElaboration elseElaboration =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution lowered typing
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elaborateReturnBody?_evaluates_iff thenElaboration.complete sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elaborateReturnBody?_evaluates_iff elseElaboration.complete sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elaborateReturnBody?_evaluates_iff thenElaboration.complete sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elaborateReturnBody?_evaluates_iff elseElaboration.complete sameIds).mpr branch)

theorem ConditionalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro resolution lowered _ thenElaboration elseElaboration =>
      have runtimeLowered := lowered
      rw [← sameIds] at runtimeLowered
      cases evaluation with
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branch.checked_toStepsWithContinuation thenElaboration.complete sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branch.checked_toStepsWithContinuation elseElaboration.complete sameIds continuation)

theorem ConditionalReturnBodyEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

theorem ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem ConditionalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateConditionalReturnBody?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, ConditionalReturnBodyEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateConditionalReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyRenamingProperties`
-/

/-! Injective identity maps retain the original condition, both checked arms,
and exact Core. No owner or runtime-entry layer is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyElaborates.mapIds
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ConditionalReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      refine .intro (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
        (thenArm.mapIds mapping injective) (elseArm.mapIds mapping injective)
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

theorem elaborateConditionalReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateConditionalReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateConditionalReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateConditionalReturnBody?]
      | nil =>
          rcases statement with ⟨ifSpan, payload⟩
          cases payload <;> try rfl
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => rfl
            | some elseBody =>
                simp only [elaborateConditionalReturnBody?,
                  elaborateLocalExpression?_mapIds mapping injective, elaborateReturnBody?_mapIds mapping injective]

namespace LocalInputs

theorem checkConditionalReturnBody?_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkConditionalReturnBody? body = inputs.checkConditionalReturnBody? body := by
  simp only [checkConditionalReturnBody?, mapIds_names, mapIds_context,
    elaborateConditionalReturnBody?_mapIds mapping injective]

/-- Full optional machine results agree, not only completed values. -/
theorem runConditionalReturnBody?_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runConditionalReturnBody? fuel body store =
      inputs.runConditionalReturnBody? fuel body store := by
  simp only [runConditionalReturnBody?, checkConditionalReturnBody?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyRunnerProperties`
-/

/-! Whole checking and actual typed inputs characterize completed and exhausted
conditional-body runs. Raw skipped-arm success cannot bypass checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace LocalInputs

theorem runConditionalReturnBody?_eq_some_iff {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runConditionalReturnBody? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkConditionalReturnBody? body = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runConditionalReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Fixed-fuel completion includes whole body typing, even when a raw child
evaluation could skip unsupported syntax. Both stores and the value are exact. -/
theorem runConditionalReturnBody?_done_iff_typed_cost {inputs : LocalInputs} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runConditionalReturnBody? fuel body initialStore = some (type, .done value finalStore) ↔
      ConditionalReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ cost, ConditionalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runConditionalReturnBody?_eq_some_iff.mp completed
    exact ⟨elaborateConditionalReturnBody?_sound checked,
      (elaborateConditionalReturnBody?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := conditionalReturnBodyHasType_iff_elaborates.mp typing
    exact runConditionalReturnBody?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

/-- Typed inputs give a typed value and both exact fuel boundaries, for any
initial store. Exhaustion states are existential, not identified with each other. -/
theorem conditionalReturnBody_typed_cost_execution {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ConditionalReturnBodyHasType inputs.names inputs.context body type) (store : Core.Store) :
    ∃ value cost, ConditionalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runConditionalReturnBody? fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runConditionalReturnBody? fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := conditionalReturnBodyHasType_iff_elaborates.mp typing
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates inputs.sameIds inputs.environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked inputs.sameIds
    (fuel := fuel)) (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds (fuel := fuel))
  simpa only [runConditionalReturnBody?, checkConditionalReturnBody?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

/-- Present exhaustion requires whole body typing and an independent cost
strictly above the supplied fuel. No particular suspended state is prescribed. -/
theorem runConditionalReturnBody?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runConditionalReturnBody? fuel body store = some (type, .outOfFuel suspended)) ↔
      ConditionalReturnBodyHasType inputs.names inputs.context body type ∧
      ∃ value cost, ConditionalReturnBodyEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runConditionalReturnBody?_eq_some_iff.mp exhausted
    have typing := elaborateConditionalReturnBody?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ := conditionalReturnBody_typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, runConditionalReturnBody?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unsupported bodies fail checking; checked bodies either complete or exhaust
their fuel. Neither path returns a machine fault, including with an arbitrary store. -/
theorem runConditionalReturnBody?_never_faults (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runConditionalReturnBody? fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runConditionalReturnBody?_eq_some_iff.mp fault
  have typing := elaborateConditionalReturnBody?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ := conditionalReturnBody_typed_cost_execution typing store
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
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyFuelBoundProperties`
-/

/-! A conservative bound includes the larger written return arm. Zero for an
unsupported whole shape does not certify acceptance or execution. -/

set_option autoImplicit false

namespace Solcore.Frontend

def conditionalReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .ifThen condition thenBody (some elseBody)⟩] =>
      localExpressionFuelBound condition + max (returnBodyFuelBound thenBody) (returnBodyFuelBound elseBody) + 2
  | _ => 0

theorem ConditionalReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ conditionalReturnBodyFuelBound body := by
  cases evaluation with
  | ifTrue condition branch =>
      have conditionBound := condition.cost_le_fuelBound
      have branchBound := branch.cost_le_fuelBound
      simp only [conditionalReturnBodyFuelBound]
      omega
  | ifFalse condition branch =>
      have conditionBound := condition.cost_le_fuelBound
      have branchBound := branch.cost_le_fuelBound
      simp only [conditionalReturnBodyFuelBound]
      omega

theorem elaborateConditionalReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : conditionalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateConditionalReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runConditionalReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : ConditionalReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : conditionalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runConditionalReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.conditionalReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyResumptionProperties`
-/

/-! Resume only the actual suspended state, with its pending conditional or arm
frames intact. Elaboration remains unchanged across every execution chunk. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runConditionalReturnBody?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runConditionalReturnBody? spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runConditionalReturnBody? (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runConditionalReturnBody?_eq_some_iff.mp exhausted
  exact runConditionalReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ConditionalReturnBodyStoreProperties`
-/

/-! Store replay preserves values and costs, while full states retain their
own stores. Completed observations and exhaustion presence are related. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : ConditionalReturnBodyEvaluates table environment replacement body value replacement := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue (condition.change_store replacement) (branch.change_store replacement)
  | ifFalse condition branch => exact .ifFalse (condition.change_store replacement) (branch.change_store replacement)

theorem ConditionalReturnBodyEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : ConditionalReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue (condition.change_store replacement) (branch.change_store replacement)
  | ifFalse condition branch => exact .ifFalse (condition.change_store replacement) (branch.change_store replacement)

theorem conditionalReturnBodyEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ConditionalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ ConditionalReturnBodyEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem conditionalReturnBodyEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        ConditionalReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runConditionalReturnBody?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runConditionalReturnBody? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runConditionalReturnBody? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runConditionalReturnBody?_done_iff_typed_cost, LocalInputs.runConditionalReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runConditionalReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runConditionalReturnBody? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runConditionalReturnBody? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runConditionalReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runConditionalReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.TerminalReturnBody
/-! A nonrecursive body-only union of singleton returns and terminal if/else.
The original adapters retain their contracts; the union adds no Core operation.
Conditional arms remain singleton returns, not recursive terminal bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Dispatch by original whole-body shape, retaining exact successful Core and
type results. Unsupported or malformed children receive no fallback meaning. -/
def elaborateTerminalReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt _⟩] => elaborateReturnBody? table context body
  | [⟨_, .ifThen _ _ (some _)⟩] => elaborateConditionalReturnBody? table context body
  | _ => none

inductive TerminalReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | single {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType table context body type) :
      TerminalReturnBodyHasType table context body type
  | conditional {body : Syntax.Block} {type : Core.Ty}
      (child : ConditionalReturnBodyHasType table context body type) :
      TerminalReturnBodyHasType table context body type

inductive TerminalReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates table context body core type) :
      TerminalReturnBodyElaborates table context body core type
  | conditional {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ConditionalReturnBodyElaborates table context body core type) :
      TerminalReturnBodyElaborates table context body core type

namespace LocalInputs

def checkTerminalReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateTerminalReturnBody? inputs.names inputs.context body

/-- Execute the retained checked Core with the original ordered runtime values;
fuel exhaustion remains a present machine result. -/
def runTerminalReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTerminalReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyEvaluation`
-/

/-! A nonrecursive union of existing raw return-body semantics. The wrapper
adds no source control operation, value conversion, store effect or cost. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TerminalReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnBodyEvaluates table environment initialStore body value finalStore
  | conditional {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnBodyEvaluates table environment initialStore body value finalStore

inductive TerminalReturnBodyEvaluatesWithCost (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost
  | conditional {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyEvaluationProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyProperties`
-/

/-! Exact static union laws retain the two original body profiles. Embeddings
preserve the whole optional checker result, including unsupported children. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnBody?_single (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := rfl

theorem elaborateTerminalReturnBody?_conditional (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := rfl

theorem ReturnBodyElaborates.terminal_complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  have accepted := elaboration.complete
  cases elaboration <;> exact accepted

theorem ConditionalReturnBodyElaborates.terminal_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  have accepted := elaboration.complete
  cases elaboration
  exact accepted

theorem TerminalReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | single child => exact child.terminal_complete
  | conditional child => exact child.terminal_complete

theorem elaborateTerminalReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    TerminalReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
      | nil =>
          rcases statement with ⟨statementSpan, payload⟩
          cases payload <;> try simp only [elaborateTerminalReturnBody?, reduceCtorEq] at accepted
          case returnStmt returned => exact .single (elaborateReturnBody?_elaborates accepted)
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => simp only [reduceCtorEq] at accepted
            | some elseBody => exact .conditional (elaborateConditionalReturnBody?_elaborates accepted)

theorem elaborateTerminalReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTerminalReturnBody? table context body = some (core, type) ↔
      TerminalReturnBodyElaborates table context body core type :=
  ⟨elaborateTerminalReturnBody?_elaborates, TerminalReturnBodyElaborates.complete⟩

theorem TerminalReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    TerminalReturnBodyHasType table context body type := by
  cases elaboration with
  | single child => exact .single child.hasType
  | conditional child => exact .conditional child.hasType

theorem TerminalReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    ∃ core, TerminalReturnBodyElaborates table context body core type := by
  cases typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | conditional child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .conditional elaboration⟩

theorem TerminalReturnBodyHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    ∃ core, elaborateTerminalReturnBody? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTerminalReturnBody?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    TerminalReturnBodyHasType table context body type :=
  (elaborateTerminalReturnBody?_elaborates accepted).hasType

theorem terminalReturnBodyHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} : TerminalReturnBodyHasType table context body type ↔
      ∃ core, elaborateTerminalReturnBody? table context body = some (core, type) :=
  ⟨TerminalReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTerminalReturnBody?_sound accepted⟩

theorem elaborateTerminalReturnBody?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaborateTerminalReturnBody?_elaborates accepted with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | conditional child => exact elaborateConditionalReturnBody?_core_hasType child.complete

theorem TerminalReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TerminalReturnBodyElaborates table context body leftCore leftType)
    (right : TerminalReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TerminalReturnBodyHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TerminalReturnBodyHasType table context body left)
    (second : TerminalReturnBodyHasType table context body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTerminalReturnBody?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateTerminalReturnBody? table context body = none ↔
      ¬ ∃ type, TerminalReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTerminalReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTerminalReturnBody?_sound result⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyExecutionProperties`
-/

/-! The terminal wrapper preserves the exact component Core and all runtime
endpoints. The independent elaboration selects a disjoint source shape. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnBody?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TerminalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaborateTerminalReturnBody?_elaborates accepted with
  | single elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => exact (elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
        | conditional child => cases elaboration <;> cases child
      · intro evaluation
        exact .single ((elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)
  | conditional elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child <;> cases elaboration
        | conditional child => exact (elaborateConditionalReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
      · intro evaluation
        exact .conditional ((elaborateConditionalReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)

theorem TerminalReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases evaluation with
  | single child =>
      cases elaborateTerminalReturnBody?_elaborates accepted with
      | single elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation
      | conditional elaboration => cases child <;> cases elaboration
  | conditional child =>
      cases elaborateTerminalReturnBody?_elaborates accepted with
      | single elaboration => cases elaboration <;> cases child
      | conditional elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation

theorem TerminalReturnBodyEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

theorem TerminalReturnBodyEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TerminalReturnBodyEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTerminalReturnBody?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, TerminalReturnBodyEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTerminalReturnBody?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyRenamingProperties`
-/

/-! The nonrecursive terminal union preserves exact component elaboration and
all optional checker/runner results under injective identity relabeling. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnBodyElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnBodyElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  cases elaboration with
  | single child => exact .single (child.mapIds mapping injective)
  | conditional child => exact .conditional (child.mapIds mapping injective)

theorem elaborateTerminalReturnBody?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateTerminalReturnBody? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateTerminalReturnBody? table context body := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => rfl
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateTerminalReturnBody?]
      | nil =>
          rcases statement with ⟨statementSpan, payload⟩
          cases payload <;> try rfl
          case returnStmt returned =>
            exact elaborateReturnBody?_mapIds mapping injective table context
              ⟨blockSpan, [⟨statementSpan, .returnStmt returned⟩]⟩
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => rfl
            | some elseBody =>
                exact elaborateConditionalReturnBody?_mapIds mapping injective table context
                  ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩

namespace LocalInputs

theorem checkTerminalReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkTerminalReturnBody? body = inputs.checkTerminalReturnBody? body := by
  simp only [checkTerminalReturnBody?, mapIds_names, mapIds_context,
    elaborateTerminalReturnBody?_mapIds mapping injective]

/-- Relabeling changes no positional runtime value, including at insufficient fuel. -/
theorem runTerminalReturnBody?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runTerminalReturnBody? fuel body store =
      inputs.runTerminalReturnBody? fuel body store := by
  simp only [runTerminalReturnBody?, checkTerminalReturnBody?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyRunnerProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyFuelBoundProperties`
-/

/-! Shape dispatch preserves the component source bound without extra cost.
An unsupported shape still receives zero and must pass checking before running. -/

set_option autoImplicit false

namespace Solcore.Frontend

def terminalReturnBodyFuelBound (body : Syntax.Block) : Nat :=
  match body.value with
  | [⟨_, .returnStmt _⟩] => returnBodyFuelBound body
  | [⟨_, .ifThen _ _ (some _)⟩] => conditionalReturnBodyFuelBound body
  | _ => 0

theorem TerminalReturnBodyEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ terminalReturnBodyFuelBound body := by
  cases evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> exact bounded
  | conditional child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> exact bounded

theorem elaborateTerminalReturnBody?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTerminalReturnBody?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTerminalReturnBody?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnBodyHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnBodyFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTerminalReturnBody? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.terminalReturnBody_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyResumptionProperties`
-/

/-! Resume only the actual suspended state, with its pending expression,
conditional or arm frames intact. Elaboration is unchanged across chunks. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTerminalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTerminalReturnBody?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTerminalReturnBody? spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTerminalReturnBody? (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTerminalReturnBody?_eq_some_iff.mp exhausted
  exact runTerminalReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnBodyStoreProperties`
-/

/-! Store replay preserves values and costs, while full states retain their
own stores. Completed observations and exhaustion presence are related. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnBodyEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : TerminalReturnBodyEvaluates table environment replacement body value replacement := by
  cases evaluation with
  | single child => exact .single (child.change_store replacement)
  | conditional child => exact .conditional (child.change_store replacement)

theorem TerminalReturnBodyEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : TerminalReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  cases evaluation with
  | single child => exact .single (child.change_store replacement)
  | conditional child => exact .conditional (child.change_store replacement)

theorem terminalReturnBodyEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TerminalReturnBodyEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ TerminalReturnBodyEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem terminalReturnBodyEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TerminalReturnBodyEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runTerminalReturnBody?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTerminalReturnBody? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTerminalReturnBody? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTerminalReturnBody?_done_iff_typed_cost, LocalInputs.runTerminalReturnBody?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runTerminalReturnBody?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runTerminalReturnBody? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTerminalReturnBody? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTerminalReturnBody?_outOfFuel_iff_typed_cost, LocalInputs.runTerminalReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.TerminalReturnTree
/-! A separate recursive body adapter: singleton returns at the leaves and
singleton explicit if/else nodes. Every written branch is checked. Existing
nonrecursive body and runtime-function entry profiles remain unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Structural recursion on the original block has no depth or fuel limit.
Keep the exact condition and both ordered arms; add no Core operation. -/
def elaborateTerminalReturnTree? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => elaborateReturnBody? table context body
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? table context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateTerminalReturnTree? table context thenBody
        let (elseCore, elseType) ← elaborateTerminalReturnTree? table context elseBody
        if thenType = elseType then
          return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none
termination_by sizeOf body

inductive TerminalReturnTreeHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | single {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType table context body type) :
      TerminalReturnTreeHasType table context body type
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType table context condition .bool)
      (thenTyping : TerminalReturnTreeHasType table context thenBody type)
      (elseTyping : TerminalReturnTreeHasType table context elseBody type) :
      TerminalReturnTreeHasType table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Independent exact elaboration retains condition resolution, positional
lowering and typing, and the original recursive arm derivations separately. -/
inductive TerminalReturnTreeElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates table context body core type) :
      TerminalReturnTreeElaborates table context body core type
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionResolution : ResolvesLocalExpression table condition conditionResolved)
      (conditionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) conditionResolved conditionCore)
      (conditionTyping : Resolved.HasType context conditionResolved .bool)
      (thenElaboration : TerminalReturnTreeElaborates table context thenBody thenCore type)
      (elseElaboration : TerminalReturnTreeElaborates table context elseBody elseCore type) :
      TerminalReturnTreeElaborates table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeElaboration`
-/

/-! Exact recursive elaboration characterizes the total tree checker. Child
inversion retains both original arms, not just a selected or same-typed Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnTree?_single (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTerminalReturnTree?]

theorem elaborateTerminalReturnTree?_children
    {table : LocalNameTable} {context : Resolved.Context}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? table context condition = some (conditionCore, .bool) ∧
      elaborateTerminalReturnTree? table context thenBody = some (thenCore, type) ∧
      elaborateTerminalReturnTree? table context elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateTerminalReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

theorem TerminalReturnTreeElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) := by
  induction elaboration with
  | single child =>
      have accepted := child.complete
      cases child <;> simpa only [elaborateTerminalReturnTree?] using accepted
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      rw [elaborateTerminalReturnTree?]
      simp [elaborateLocalExpression?_complete resolution lowered typing, thenIH, elseIH]

theorem elaborateTerminalReturnTree?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    TerminalReturnTreeElaborates table context body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases rest with
          | cons next rest => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
          | nil =>
              cases statement with
              | mk statementSpan payload =>
                  cases payload <;> try simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
                  case returnStmt returned => exact .single (elaborateReturnBody?_elaborates accepted)
                  case ifThen condition thenBody optionalElse =>
                    cases optionalElse with
                    | none => simp only [elaborateTerminalReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ :=
                          elaborateTerminalReturnTree?_children (blockSpan := blockSpan) (ifSpan := statementSpan) accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ :=
                          elaborateLocalExpression?_sound conditionAccepted
                        exact .conditional resolution lowered typing
                          (elaborateTerminalReturnTree?_elaborates thenAccepted)
                          (elaborateTerminalReturnTree?_elaborates elseAccepted)
termination_by sizeOf body

theorem elaborateTerminalReturnTree?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTerminalReturnTree? table context body = some (core, type) ↔
      TerminalReturnTreeElaborates table context body core type :=
  ⟨elaborateTerminalReturnTree?_elaborates, TerminalReturnTreeElaborates.complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeEvaluation`
-/

/-! Independent recursive selected-path semantics. Unselected subtrees need
neither evaluation nor whole acceptance; both stores remain explicit. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TerminalReturnTreeEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore body value finalStore
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : TerminalReturnTreeEvaluates table environment middleStore thenBody value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : TerminalReturnTreeEvaluates table environment middleStore elseBody value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Only selected conditions and leaves contribute cost. Each conditional
adds the two existing Core transitions; the leaf wrapper adds nothing. -/
inductive TerminalReturnTreeEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : TerminalReturnTreeEvaluatesWithCost table environment
        middleStore thenBody value finalStore branchCost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : TerminalReturnTreeEvaluatesWithCost table environment
        middleStore elseBody value finalStore branchCost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeEvaluationEmbeddingProperties`
-/

/-! Every old selected-path derivation embeds with the original value, stores
and cost. Whole checking and evaluation of an unselected arm are not required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := .single evaluation

theorem ReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := .single evaluation

theorem ConditionalReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue condition branch.returnTree
  | ifFalse condition branch => exact .ifFalse condition branch.returnTree

theorem ConditionalReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue condition branch.returnTree
  | ifFalse condition branch => exact .ifFalse condition branch.returnTree

theorem TerminalReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeEvaluationProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeExecutionProperties`
-/

/-! Whole checked trees correspond to their exact Core under aligned IDs.
Runtime typing is unnecessary for correspondence; pending continuations remain
intact at the exact-cost path endpoint rather than being executed or unwound. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTerminalReturnTree?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTerminalReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing initialStore finalStore value with
  | single elaboration =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => exact (elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mp child
        | ifTrue _ _ => cases elaboration
        | ifFalse _ _ => cases elaboration
      · intro evaluation
        exact .single ((elaborateReturnBody?_evaluates_iff elaboration.complete sameIds).mpr evaluation)
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution lowered typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((thenIH (initialStore := _) (finalStore := _) (value := _)).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elseIH (initialStore := _) (finalStore := _) (value := _)).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((thenIH (initialStore := _) (finalStore := _) (value := _)).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elseIH (initialStore := _) (finalStore := _) (value := _)).mpr branch)

theorem TerminalReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction evaluation generalizing core type continuation with
  | single child =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => exact child.checked_toStepsWithContinuation elaboration.complete sameIds continuation
      | conditional _ _ _ _ _ => cases child
  | ifTrue condition _ branchIH =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => cases elaboration
      | conditional resolution lowered _ thenElaboration _ =>
          have runtimeLowered := lowered
          rw [← sameIds] at runtimeLowered
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branchIH (core := _) (type := _) (continuation := continuation) thenElaboration.complete)
  | ifFalse condition _ branchIH =>
      cases elaborateTerminalReturnTree?_elaborates accepted with
      | single elaboration => cases elaboration
      | conditional resolution lowered _ _ elseElaboration =>
          have runtimeLowered := lowered
          rw [← sameIds] at runtimeLowered
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (branchIH (core := _) (type := _) (continuation := continuation) elseElaboration.complete)

theorem TerminalReturnTreeEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeProperties`
-/

/-! Whole recursive source typing and exact elaboration agree without runtime
values. Every original arm contributes independent evidence at every depth. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    TerminalReturnTreeHasType table context body type := by
  induction elaboration with
  | single child => exact .single child.hasType
  | conditional resolution _ typing _ _ thenIH elseIH =>
      exact .conditional (resolution.reflects_type typing) thenIH elseIH

theorem TerminalReturnTreeHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnTreeHasType table context body type) :
    ∃ core, TerminalReturnTreeElaborates table context body core type := by
  induction typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore,
        .conditional resolution lowered typed thenElaboration elseElaboration⟩

theorem terminalReturnTreeHasType_iff_elaborates_exact
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} {type : Core.Ty} :
    TerminalReturnTreeHasType table context body type ↔
      ∃ core, TerminalReturnTreeElaborates table context body core type :=
  ⟨TerminalReturnTreeHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TerminalReturnTreeHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnTreeHasType table context body type) :
    ∃ core, elaborateTerminalReturnTree? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTerminalReturnTree?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    TerminalReturnTreeHasType table context body type :=
  (elaborateTerminalReturnTree?_elaborates accepted).hasType

theorem terminalReturnTreeHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} {type : Core.Ty} :
    TerminalReturnTreeHasType table context body type ↔
      ∃ core, elaborateTerminalReturnTree? table context body = some (core, type) :=
  ⟨TerminalReturnTreeHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTerminalReturnTree?_sound accepted⟩

theorem elaborateTerminalReturnTree?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  have elaboration := elaborateTerminalReturnTree?_elaborates accepted
  clear accepted
  induction elaboration with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | conditional _ lowered typing _ _ thenIH elseIH =>
      exact .ifE (lowered.preserves_type typing) thenIH elseIH

/-- The whole checked tree fixes the exact Core as well as its type. Equal
types alone do not permit a different ordering or choice of return leaves. -/
theorem TerminalReturnTreeElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TerminalReturnTreeElaborates table context body leftCore leftType)
    (right : TerminalReturnTreeElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TerminalReturnTreeHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TerminalReturnTreeHasType table context body left)
    (second : TerminalReturnTreeHasType table context body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTerminalReturnTree?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateTerminalReturnTree? table context body = none ↔
      ¬ ∃ type, TerminalReturnTreeHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTerminalReturnTree? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTerminalReturnTree?_sound result⟩)

/-- Only the enclosing block and statement spans change. The original condition
and arbitrarily deep ordered child blocks remain identical. -/
theorem elaborateTerminalReturnTree?_spans (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan otherBlockSpan otherIfSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateTerminalReturnTree? table context
        ⟨otherBlockSpan, [⟨otherIfSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := by
  simp only [elaborateTerminalReturnTree?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeEmbeddingProperties`
-/

/-! Old successful body judgments embed exactly. Full optional-result equality
is confined to old singleton and one-level shapes, not arbitrary return trees. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := .single typing

theorem ReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := .single elaboration

theorem ReturnBodyElaborates.returnTree_complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem ConditionalReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := by
  cases typing with
  | intro condition thenArm elseArm => exact .conditional condition thenArm.returnTree elseArm.returnTree

theorem ConditionalReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      exact .conditional resolution lowered typing thenArm.returnTree elseArm.returnTree

theorem ConditionalReturnBodyElaborates.returnTree_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem TerminalReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := by
  cases typing with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := by
  cases elaboration with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyElaborates.returnTree_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem elaborateTerminalReturnTree?_single_terminal (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateTerminalReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTerminalReturnTree?_single, elaborateTerminalReturnBody?_single]

/-- Both arm shapes are explicitly singleton returns. Unsupported expressions
remain rejected equally; recursive arm blocks are deliberately not quantified. -/
theorem elaborateTerminalReturnTree?_conditional_singletons
    (table : LocalNameTable) (context : Resolved.Context) (condition : Syntax.Expr)
    (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  simp only [elaborateTerminalReturnTree?, elaborateConditionalReturnBody?]

theorem elaborateTerminalReturnTree?_conditional_singletons_terminal
    (table : LocalNameTable) (context : Resolved.Context) (condition : Syntax.Expr)
    (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateTerminalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  rw [elaborateTerminalReturnBody?_conditional]
  exact elaborateTerminalReturnTree?_conditional_singletons table context condition thenReturned elseReturned
    blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeRunner`
-/

/-! Execute only the actual checked recursive Core with the original ordered
typed input values. No source-call or runtime-function profile is changed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTerminalReturnTree? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateTerminalReturnTree? inputs.names inputs.context body

/-- Check failure is absent; a checked run retains its complete machine result,
including the genuine suspended state. Values are not reordered here. -/
def runTerminalReturnTree? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTerminalReturnTree? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeRenamingProperties`
-/

/-! Injective identity relabeling retains all recursive source children, exact
Core and complete same-fuel results without importing runtime-function entry. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeElaborates.mapIds {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeElaborates (LocalNameTable.mapIds mapping table)
      (Resolved.LocalScope.mapIds mapping context) body core type := by
  induction elaboration with
  | single child => exact .single (child.mapIds mapping injective)
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      refine .conditional (resolution.mapIds mapping) ?_
        ((Resolved.typing_renameIds_iff mapping injective).mpr typing) thenIH elseIH
      rw [Resolved.LocalScope.ids_mapIds]
      exact (Resolved.lowers_renameIds_iff mapping injective).mpr lowered

/-- Structural recursion retains failures as well as successful exact Core. -/
theorem elaborateTerminalReturnTree?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (body : Syntax.Block) :
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) body =
      elaborateTerminalReturnTree? table context body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTerminalReturnTree?]
      | cons statement rest =>
          cases rest with
          | cons next rest => simp only [elaborateTerminalReturnTree?]
          | nil =>
              cases statement with
              | mk statementSpan payload =>
                  cases payload <;> try simp only [elaborateTerminalReturnTree?]
                  case returnStmt returned =>
                    exact elaborateReturnBody?_mapIds mapping injective table context
                      ⟨blockSpan, [⟨statementSpan, .returnStmt returned⟩]⟩
                  case ifThen condition thenBody optionalElse =>
                    cases optionalElse with
                    | none => simp only [elaborateTerminalReturnTree?]
                    | some elseBody =>
                        rw [elaborateTerminalReturnTree?, elaborateTerminalReturnTree?]
                        rw [elaborateLocalExpression?_mapIds mapping injective,
                          elaborateTerminalReturnTree?_mapIds mapping injective table context thenBody,
                          elaborateTerminalReturnTree?_mapIds mapping injective table context elseBody]
termination_by sizeOf body

namespace LocalInputs

theorem checkTerminalReturnTree?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (body : Syntax.Block) :
    (inputs.mapIds mapping injective).checkTerminalReturnTree? body = inputs.checkTerminalReturnTree? body := by
  simp only [checkTerminalReturnTree?, mapIds_names, mapIds_context,
    elaborateTerminalReturnTree?_mapIds mapping injective]

/-- Every optional result agrees, including actual checkpoints at insufficient
fuel. Relabeling does not reverse or otherwise reorder positional values. -/
theorem runTerminalReturnTree?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds mapping injective).runTerminalReturnTree? fuel body store =
      inputs.runTerminalReturnTree? fuel body store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?_mapIds,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeRunnerEmbeddingProperties`
-/

/-! Old-shape runner equality retains failure and every actual Core result.
Singleton arms are explicit; this does not identify old and recursive runners
on arbitrary deep bodies rejected by the old profile. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTerminalReturnTree?_single (inputs : LocalInputs) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runReturnBody?, checkReturnBody?,
    elaborateTerminalReturnTree?_single]

theorem runTerminalReturnTree?_single_terminal (inputs : LocalInputs) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runTerminalReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runTerminalReturnBody?, checkTerminalReturnBody?,
    elaborateTerminalReturnTree?_single_terminal]

theorem runTerminalReturnTree?_conditional_singletons (inputs : LocalInputs) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runConditionalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runConditionalReturnBody?, checkConditionalReturnBody?,
    elaborateTerminalReturnTree?_conditional_singletons]

theorem runTerminalReturnTree?_conditional_singletons_terminal (inputs : LocalInputs) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runTerminalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runTerminalReturnBody?, checkTerminalReturnBody?,
    elaborateTerminalReturnTree?_conditional_singletons_terminal]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeRunnerProperties`
-/

/-! Exact fuel thresholds require a checked terminating path. At the typed
input boundary, whole checking supplies such a path and excludes faults. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TerminalReturnTreeEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTerminalReturnTree?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, TerminalReturnTreeEvaluatesWithCost table environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTerminalReturnTree?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

namespace LocalInputs

theorem runTerminalReturnTree?_eq_none_iff {inputs : LocalInputs} {body : Syntax.Block}
    {fuel : Nat} {store : Core.Store} :
    inputs.runTerminalReturnTree? fuel body store = none ↔ inputs.checkTerminalReturnTree? body = none := by
  cases checked : inputs.checkTerminalReturnTree? body with
  | none => simp [runTerminalReturnTree?, checked]
  | some pair =>
      rcases pair with ⟨core, type⟩
      simp [runTerminalReturnTree?, checked]

theorem runTerminalReturnTree?_eq_some_iff {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runTerminalReturnTree? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkTerminalReturnTree? body = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runTerminalReturnTree?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Fixed-fuel completion includes whole body typing, even when a raw child
evaluation could skip unsupported syntax. Both stores and the value are exact. -/
theorem runTerminalReturnTree?_done_iff_typed_cost {inputs : LocalInputs} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTerminalReturnTree? fuel body initialStore = some (type, .done value finalStore) ↔
      TerminalReturnTreeHasType inputs.names inputs.context body type ∧
      ∃ cost, TerminalReturnTreeEvaluatesWithCost inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runTerminalReturnTree?_eq_some_iff.mp completed
    exact ⟨elaborateTerminalReturnTree?_sound checked,
      (elaborateTerminalReturnTree?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := terminalReturnTreeHasType_iff_elaborates.mp typing
    exact runTerminalReturnTree?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

/-- Typed inputs give a typed value and both exact fuel boundaries, for any
initial store. Exhaustion states are existential, not identified with each other. -/
theorem terminalReturnTree_typed_cost_execution {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type) (store : Core.Store) :
    ∃ value cost, TerminalReturnTreeEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runTerminalReturnTree? fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runTerminalReturnTree? fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := terminalReturnTreeHasType_iff_elaborates.mp typing
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates inputs.sameIds inputs.environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked inputs.sameIds
    (fuel := fuel)) (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds (fuel := fuel))
  simpa only [runTerminalReturnTree?, checkTerminalReturnTree?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

/-- Present exhaustion requires whole body typing and an independent cost
strictly above the supplied fuel. No particular suspended state is prescribed. -/
theorem runTerminalReturnTree?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runTerminalReturnTree? fuel body store = some (type, .outOfFuel suspended)) ↔
      TerminalReturnTreeHasType inputs.names inputs.context body type ∧
      ∃ value cost, TerminalReturnTreeEvaluatesWithCost inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runTerminalReturnTree?_eq_some_iff.mp exhausted
    have typing := elaborateTerminalReturnTree?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ := terminalReturnTree_typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, runTerminalReturnTree?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unsupported bodies fail checking; checked bodies either complete or exhaust
their fuel. Neither path returns a machine fault, including with an arbitrary store. -/
theorem runTerminalReturnTree?_never_faults (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runTerminalReturnTree? fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runTerminalReturnTree?_eq_some_iff.mp fault
  have typing := elaborateTerminalReturnTree?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ := terminalReturnTree_typed_cost_execution typing store
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
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeFuelBoundProperties`
-/

/-! A total source-only budget includes the larger recursive arm. This is an
upper bound, not a minimum fuel threshold or a substitute for whole checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

def terminalReturnTreeFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => returnBodyFuelBound body
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      localExpressionFuelBound condition +
        max (terminalReturnTreeFuelBound thenBody) (terminalReturnTreeFuelBound elseBody) + 2
  | _ => 0
termination_by sizeOf body

/-- Raw selected-path costs are bounded even when a written unselected subtree
is unsupported. The numerical bound alone supplies no acceptance evidence. -/
theorem TerminalReturnTreeEvaluatesWithCost.cost_le_fuelBound
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
    cost ≤ terminalReturnTreeFuelBound body := by
  induction evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> simpa only [terminalReturnTreeFuelBound] using bounded
  | ifTrue condition _ ih | ifFalse condition _ ih =>
      have conditionBound := condition.cost_le_fuelBound
      simp only [terminalReturnTreeFuelBound]
      omega

theorem elaborateTerminalReturnTree?_run_done_of_fuelBound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTerminalReturnTree?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTerminalReturnTree?_done_of_fuelBound
    {inputs : LocalInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (store : Core.Store) (fuel : Nat) (enough : terminalReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTerminalReturnTree? fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := inputs.terminalReturnTree_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeResumptionProperties`
-/

/-! Only a genuine exhausted state supplies a checkpoint. Its control, pending
frames, environment and store remain intact throughout exact residual execution. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTerminalReturnTree? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTerminalReturnTree?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTerminalReturnTree? spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTerminalReturnTree? (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTerminalReturnTree?_eq_some_iff.mp exhausted
  exact runTerminalReturnTree?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TerminalReturnTreeStoreProperties`
-/

/-! Independent selected paths replay at any store with identical values and
costs. Runner observations retain their own stores, not identical full states. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (replacement : Core.Store) : TerminalReturnTreeEvaluates table environment replacement body value replacement := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem TerminalReturnTreeEvaluatesWithCost.change_store
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (replacement : Core.Store) : TerminalReturnTreeEvaluatesWithCost table environment replacement body value replacement cost := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem terminalReturnTreeEvaluates_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluates table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem terminalReturnTreeEvaluatesWithCost_store_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TerminalReturnTreeEvaluatesWithCost table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Each completed observation carries its own initial store. This is not an
equality of complete run results across different stores. -/
theorem LocalInputs.runTerminalReturnTree?_done_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTerminalReturnTree? fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTerminalReturnTree? fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTerminalReturnTree?_done_iff_typed_cost, LocalInputs.runTerminalReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Only exhaustion presence is related; the actual checkpoints retain their
respective stores and are not identified with each other. -/
theorem LocalInputs.runTerminalReturnTree?_outOfFuel_store_iff
    (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) :
    (∃ checkpoint, inputs.runTerminalReturnTree? fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTerminalReturnTree? fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost, LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
end
