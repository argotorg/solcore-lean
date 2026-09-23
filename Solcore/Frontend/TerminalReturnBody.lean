import Solcore.Frontend.ConditionalReturnBody
import Solcore.Core.FuelResumptionProperties

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
