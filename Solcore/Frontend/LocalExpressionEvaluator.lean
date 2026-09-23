import Solcore.Frontend.LocalReference
import Solcore.Frontend.WordLiteral
import Solcore.Resolved.Eval
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Resolved.LocalScope

/-! Direct execution of the existing raw source fragment, without resolution,
typing, lowering or Core execution. Output costs count existing Core transitions,
not source traversal. A successful selected path does not imply whole checking. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Strict Word results and their existing lowering overhead. Short-circuit
operators have no strict Word meaning at this boundary. -/
def evaluateLocalWordBinaryWithCost? (operator : Syntax.BinaryOp) (left right : Core.Word) :
    Option (Core.Value × Nat) :=
  match operator with
  | .add => some (.word (left.add right), 3)
  | .subtract => some (.word (left.sub right), 3)
  | .multiply => some (.word (left.mul right), 3)
  | .divide => some (.word (left.udiv right), 3)
  | .modulo => some (.word (left.umod right), 3)
  | .bitAnd => some (.word (left.bitAnd right), 3)
  | .bitOr => some (.word (left.bitOr right), 3)
  | .bitXor => some (.word (left.bitXor right), 3)
  | .greater => some (.bool (decide (left > right)), 3)
  | .less => some (.bool (decide (left < right)), 9)
  | .equal => some (.bool (left == right), 3)
  | .notEqual => some (.bool (!(left == right)), 5)
  | .lessEqual => some (.bool (!(decide (left > right))), 5)
  | .greaterEqual => some (.bool (!(decide (left < right))), 11)
  | .logicalAnd | .logicalOr => none

/-- First-match actual lookup, strict primitives/right-associated tuples and selected-only control
flow. No store, type context, alignment, uniqueness or spelling validity is needed.
`none` denotes raw evaluation absence, not source-language invalidity. -/
def evaluateLocalExpressionWithCost? (table : LocalNameTable) (environment : Resolved.Environment)
    (source : Syntax.Expr) : Option (Core.Value × Nat) :=
  match source with
  | ⟨_, .identifier name⟩ => do
      let id ← table.lookup? name.value
      let value ← environment.lookup? id
      return (value, 1)
  | ⟨_, .literal literal⟩ => do
      return (.word (← interpretWordLiteral? literal), 1)
  | ⟨_, .group inner⟩ => evaluateLocalExpressionWithCost? table environment inner
  | ⟨_, .tuple ⟨_, []⟩⟩ => some (.unit, 1)
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
      let (leftValue, leftCost) ← evaluateLocalExpressionWithCost? table environment left
      let (rightValue, rightCost) ← evaluateLocalExpressionWithCost? table environment right
      return (.pair leftValue rightValue, leftCost + rightCost + 3)
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ => do
      let (headValue, headCost) ← evaluateLocalExpressionWithCost? table environment first
      let (tailValue, tailCost) ← evaluateLocalExpressionWithCost? table environment
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return (.pair headValue tailValue, headCost + tailCost + 3)
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
      let (.bool value, cost) ← evaluateLocalExpressionWithCost? table environment operand | none
      return (.bool (!value), cost + 2)
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
      let (.word value, cost) ← evaluateLocalExpressionWithCost? table environment operand | none
      return (.word value.bitNot, cost + 2)
  | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
      let (.bool choice, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      if choice then
        let (value, rightCost) ← evaluateLocalExpressionWithCost? table environment right
        return (value, leftCost + rightCost + 2)
      else return (.bool false, leftCost + 3)
  | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
      let (.bool choice, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      if choice then return (.bool true, leftCost + 3)
      else
        let (value, rightCost) ← evaluateLocalExpressionWithCost? table environment right
        return (value, leftCost + rightCost + 2)
  | ⟨_, .binary left ⟨_, operator⟩ right⟩ => do
      let (.word l, leftCost) ← evaluateLocalExpressionWithCost? table environment left | none
      let (.word r, rightCost) ← evaluateLocalExpressionWithCost? table environment right | none
      let (value, overhead) ← evaluateLocalWordBinaryWithCost? operator l r
      return (value, leftCost + rightCost + overhead)
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
      let (.bool choice, conditionCost) ← evaluateLocalExpressionWithCost? table environment condition | none
      let (value, branchCost) ← if choice then evaluateLocalExpressionWithCost? table environment thenBranch
        else evaluateLocalExpressionWithCost? table environment elseBranch
      return (value, conditionCost + branchCost + 2)
  | _ => none
termination_by sizeOf source

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluatorCompletenessProperties`
-/

/-! Every independent raw derivation is executed directly on its original
syntax and caller rows. Store endpoints impose no extra evaluator premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_complete {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    evaluateLocalExpressionWithCost? table environment source = some (value, cost) := by
  induction evaluation with
  | identifier named found =>
      simp [evaluateLocalExpressionWithCost?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | wordLiteral meaning =>
      simp [evaluateLocalExpressionWithCost?, interpretWordLiteral?_complete meaning]
  | group _ ih => simpa only [evaluateLocalExpressionWithCost?] using ih
  | unit => simp only [evaluateLocalExpressionWithCost?]
  | many _ _ headIH tailIH =>
      rw [evaluateLocalExpressionWithCost?]
      simp only [headIH, tailIH, bind, Option.bind_some, pure]
  | logicalNot _ ih | bitNot _ ih | andFalse _ ih | orTrue _ ih =>
      simp [evaluateLocalExpressionWithCost?, ih]
  | pair _ _ leftIH rightIH
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH
  | divide _ _ leftIH rightIH | modulo _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | greater _ _ leftIH rightIH | less _ _ leftIH rightIH
  | equal _ _ leftIH rightIH | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH | greaterEqual _ _ leftIH rightIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH
  | ifTrue _ _ leftIH rightIH | ifFalse _ _ leftIH rightIH =>
      simp [evaluateLocalExpressionWithCost?, evaluateLocalWordBinaryWithCost?, leftIH, rightIH]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluatorSoundnessProperties`
-/

/-! Successful direct execution constructs the independent raw cost relation.
Only selected children are used; opaque selected values remain unrestricted. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_sound {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (accepted : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table environment store source value store cost := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [evaluateLocalExpressionWithCost?, reduceCtorEq] at accepted
      case identifier name =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
        exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
      case literal literal =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨word, meaning, rfl, rfl⟩ := accepted
        exact .wordLiteral (interpretWordLiteral?_sound meaning)
      case group inner => exact .group (evaluateLocalExpressionWithCost?_sound accepted store)
      case tuple elements =>
        cases elements with
        | mk tupleSpan children =>
          cases children with
          | nil =>
              simp only [evaluateLocalExpressionWithCost?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .unit
          | cons left remaining =>
            cases remaining with
            | nil => simp [evaluateLocalExpressionWithCost?] at accepted
            | cons right tail =>
              cases tail with
              | cons third rest =>
                rw [evaluateLocalExpressionWithCost?] at accepted
                simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
                obtain ⟨⟨headValue, headCost⟩, headResult, ⟨tailValue, tailCost⟩, tailResult, rfl, rfl⟩ := accepted
                exact .many (evaluateLocalExpressionWithCost?_sound headResult store)
                  (evaluateLocalExpressionWithCost?_sound tailResult store)
              | nil =>
                simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff,
                  pure, Option.some.injEq, Prod.mk.injEq] at accepted
                obtain ⟨⟨leftValue, leftCost⟩, leftResult, ⟨rightValue, rightCost⟩, rightResult, rfl, rfl⟩ := accepted
                exact .pair (evaluateLocalExpressionWithCost?_sound leftResult store)
                  (evaluateLocalExpressionWithCost?_sound rightResult store)
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
        all_goals
          obtain ⟨⟨actual, childCost⟩, child, result⟩ := accepted
          cases actual <;> simp only [pure, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .logicalNot (evaluateLocalExpressionWithCost?_sound child store)
          | exact .bitNot (evaluateLocalExpressionWithCost?_sound child store)
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue
        case logicalAnd =>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, leftCost⟩, leftResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice
          · simp only [Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .andFalse (evaluateLocalExpressionWithCost?_sound leftResult store)
          · simp only [↓reduceIte, Option.bind_eq_some_iff] at result
            obtain ⟨⟨actual, rightCost⟩, rightResult, result⟩ := result
            simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .andTrue (evaluateLocalExpressionWithCost?_sound leftResult store)
              (evaluateLocalExpressionWithCost?_sound rightResult store)
        case logicalOr =>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, leftCost⟩, leftResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
            obtain ⟨⟨actual, rightCost⟩, rightResult, result⟩ := result
            simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .orFalse (evaluateLocalExpressionWithCost?_sound leftResult store)
              (evaluateLocalExpressionWithCost?_sound rightResult store)
          · simp only [↓reduceIte, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .orTrue (evaluateLocalExpressionWithCost?_sound leftResult store)
        all_goals
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actualLeft, leftCost⟩, leftResult, result⟩ := accepted
          cases actualLeft <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
          obtain ⟨⟨actualRight, rightCost⟩, rightResult, result⟩ := result
          cases actualRight <;> simp only [reduceCtorEq, evaluateLocalWordBinaryWithCost?,
            Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .add (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .subtract (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .multiply (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .divide (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .modulo (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitAnd (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitOr (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitXor (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .greater (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .less (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .equal (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .notEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .lessEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .greaterEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
      case conditional condition question thenBranch colon elseBranch =>
        simp only [bind, Option.bind_eq_some_iff] at accepted
        obtain ⟨⟨actual, conditionCost⟩, conditionResult, result⟩ := accepted
        cases actual <;> simp only [reduceCtorEq] at result
        rename_i choice
        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
        all_goals
          obtain ⟨⟨actual, branchCost⟩, branchResult, result⟩ := result
          simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .ifTrue (evaluateLocalExpressionWithCost?_sound conditionResult store) (evaluateLocalExpressionWithCost?_sound branchResult store)
          | exact .ifFalse (evaluateLocalExpressionWithCost?_sound conditionResult store) (evaluateLocalExpressionWithCost?_sound branchResult store)
termination_by sizeOf source

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluatorProperties`
-/

/-! Exact optional results characterize raw source evaluation, not acceptance.
The store-free result does not erase a general derivation's store equality. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (store : Core.Store) :
    evaluateLocalExpressionWithCost? table environment source = some (value, cost) ↔
      LocalExpressionEvaluatesWithCost table environment store source value store cost :=
  ⟨fun accepted => evaluateLocalExpressionWithCost?_sound accepted store,
    evaluateLocalExpressionWithCost?_complete⟩

theorem localExpressionEvaluatesWithCost_iff_evaluate {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateLocalExpressionWithCost? table environment source = some (value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluateLocalExpressionWithCost?_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluateLocalExpressionWithCost?_sound accepted _

theorem evaluateLocalExpressionWithCost?_eq_none_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} (store : Core.Store) :
    evaluateLocalExpressionWithCost? table environment source = none ↔
      ¬ ∃ value cost, LocalExpressionEvaluatesWithCost table environment store source value store cost := by
  constructor
  · intro absent ⟨value, cost, evaluation⟩
    have accepted := evaluateLocalExpressionWithCost?_complete evaluation
    rw [absent] at accepted
    cases accepted
  · intro absent
    cases result : evaluateLocalExpressionWithCost? table environment source with
    | none => rfl
    | some pair =>
        exact False.elim (absent ⟨pair.1, pair.2, evaluateLocalExpressionWithCost?_sound result store⟩)

theorem evaluateLocalExpressionWithCost?_exists_cost_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value}
    (store : Core.Store) :
    (∃ cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost)) ↔
      LocalExpressionEvaluates table environment store source value store := by
  constructor
  · rintro ⟨cost, accepted⟩
    exact (evaluateLocalExpressionWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, evaluateLocalExpressionWithCost?_complete costed⟩

theorem evaluateLocalExpressionWithCost?_value_iff {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value}
    (store : Core.Store) :
    (evaluateLocalExpressionWithCost? table environment source).map Prod.fst = some value ↔
      LocalExpressionEvaluates table environment store source value store := by
  constructor
  · intro projected
    obtain ⟨⟨actual, cost⟩, accepted, same⟩ := Option.map_eq_some_iff.mp projected
    cases same
    exact (evaluateLocalExpressionWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, accepted⟩ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mpr evaluation
    simp only [accepted, Option.map_some]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluatorExecutionProperties`
-/

/-! Direct source results meet the existing checked machine only through whole
checking and actual identity alignment. Raw success alone supplies neither.
Retained-continuation paths end before the continuation executes. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret value, continuation, store⟩ := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have runtimeLowered : Resolved.Lowers environment.ids resolved core := by rw [sameIds]; exact lowered
  exact (evaluateLocalExpressionWithCost?_sound evaluated store).toStepsWithContinuation resolution runtimeLowered continuation

theorem evaluateLocalExpressionWithCost?_checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values store) = .done value store ↔ cost ≤ fuel :=
  (evaluateLocalExpressionWithCost?_sound evaluated store).checked_runStateful_done_iff accepted sameIds

theorem evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {value : Core.Value} {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty}
    {store : Core.Store}
    (evaluated : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) :
    (∃ checkpoint, Core.runStateful fuel (Core.State.initial core environment.values store) = .outOfFuel checkpoint) ↔ fuel < cost :=
  (evaluateLocalExpressionWithCost?_sound evaluated store).checked_runStateful_outOfFuel_iff accepted sameIds

/-- Completion reflection retains the final store explicitly and needs no runtime
typing. Its checked lowering must still agree with the actual identity order. -/
theorem elaborateLocalExpression?_run_done_iff_evaluator
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      finalStore = initialStore ∧ ∃ cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧ cost ≤ fuel := by
  rw [elaborateLocalExpression?_run_done_iff_cost accepted sameIds]
  constructor
  · rintro ⟨cost, evaluated, enough⟩
    exact ⟨evaluated.store_eq, cost, evaluateLocalExpressionWithCost?_complete evaluated, enough⟩
  · rintro ⟨rfl, cost, evaluated, enough⟩
    exact ⟨cost, evaluateLocalExpressionWithCost?_sound evaluated _, enough⟩

theorem elaborateLocalExpression?_typed_evaluator_exists
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : environment.ids = context.ids)
    (environmentTyped : Core.EnvironmentHasTypes environment.values context.values) :
    ∃ value cost, evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧ Core.ValueHasType value type := by
  obtain ⟨value, cost, evaluated, typed, _⟩ := elaborateLocalExpression?_typed_cost_execution accepted sameIds environmentTyped []
  exact ⟨value, cost, evaluateLocalExpressionWithCost?_complete evaluated, typed⟩

namespace LocalInputs

/-- The original whole-typing conjunct cannot be replaced by raw success. -/
theorem run?_done_iff_evaluator {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.run? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧ finalStore = initialStore ∧
      ∃ cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧ cost ≤ fuel := by
  rw [run?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluated, enough⟩
    exact ⟨typing, evaluated.store_eq, cost, evaluateLocalExpressionWithCost?_complete evaluated, enough⟩
  · rintro ⟨typing, rfl, cost, evaluated, enough⟩
    exact ⟨typing, cost, evaluateLocalExpressionWithCost?_sound evaluated _, enough⟩

theorem run?_outOfFuel_iff_evaluator {inputs : LocalInputs} {source : Syntax.Expr}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ checkpoint, inputs.run? fuel source store = some (type, .outOfFuel checkpoint)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ value cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧ fuel < cost := by
  rw [run?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateLocalExpressionWithCost?_complete evaluated, short⟩
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateLocalExpressionWithCost?_sound evaluated store, short⟩

theorem typed_evaluator_execution {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value cost, evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (value, cost) ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (inputs.run? fuel source store = some (type, .done value store) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.run? fuel source store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨value, cost, evaluated, typed, boundaries⟩ := typed_cost_execution typing store
  exact ⟨value, cost, evaluateLocalExpressionWithCost?_complete evaluated, typed, boundaries⟩

end LocalInputs
end Solcore.Frontend
