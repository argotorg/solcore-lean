import Solcore.Frontend.ReturnBody
import Solcore.Core.FuelResumptionProperties

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
