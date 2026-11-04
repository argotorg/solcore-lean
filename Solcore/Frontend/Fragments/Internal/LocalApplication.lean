import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Frontend.Fragments.Internal.ExpectedLambdas
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions

/-!
# Local applications

Local applications and their runtime function.
-/

section
-- leanmerge: from Solcore.Frontend.LocalApplication
/-! Local applications and expected-lambda application forms. -/

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationReturnBody`
-/

/-! A separate original singleton return whose child is a local application.
The return retains its child's exact Core and costs without a new control frame.
Existing pure-expression and whole-function endpoints are unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateLocalApplicationReturnBody? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body.value with
  | [⟨_, .returnStmt (some source)⟩] => elaborateLocalFunctionApplication? table context source
  | _ => none

inductive LocalApplicationReturnBodyHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationHasType table context source type) :
      LocalApplicationReturnBodyHasType table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type

inductive LocalApplicationReturnBodyElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {core : Core.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationElaborates table context source core type) :
      LocalApplicationReturnBodyElaborates table context
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type

inductive LocalApplicationReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
      LocalApplicationReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore

inductive LocalApplicationReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | application {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalFunctionApplicationEvaluatesWithCost table environment
        initialStore source value finalStore cost) :
      LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost

namespace LocalInputs

def checkApplicationReturnBody? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateLocalApplicationReturnBody? inputs.names inputs.context body

/-- Preserve every checked outcome using the same actual values and store.
The input record alone does not validate allocated cells or their payloads. -/
def runApplicationReturnBody? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkApplicationReturnBody? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationReturnBodyEvaluationProperties`
-/

/-! Original singleton returns preserve their actual application's values,
stores and exact costs. Only exact Core correspondence requires aligned IDs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalApplicationReturnBodyEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore leftStore rightStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value}
    (leftEvaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body left leftStore)
    (rightEvaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases leftEvaluation with
  | application left =>
      cases rightEvaluation with
      | application right => exact left.deterministic right

theorem LocalApplicationReturnBodyEvaluatesWithCost.erase
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | application child => exact .application child.erase

theorem LocalApplicationReturnBodyEvaluates.exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore) :
    ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | application child =>
      obtain ⟨cost, counted⟩ := child.exists_cost
      exact ⟨cost, .application counted⟩

theorem localApplicationReturnBodyEvaluates_iff_exists_cost
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore ↔
      ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost :=
  ⟨LocalApplicationReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalApplicationReturnBodyEvaluatesWithCost.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore leftStore rightStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftCost rightCost : Nat}
    (leftEvaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (rightEvaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | application left =>
      cases rightEvaluation with
      | application right => exact left.deterministic right

theorem LocalApplicationReturnBodyElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalApplicationReturnBodyEvaluates table environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | application actual => exact (child.evaluates_iff sameIds).mp actual
      · intro evaluation
        exact .application ((child.evaluates_iff sameIds).mpr evaluation)

/-- Keep the same actual cost before every continuation. Pending frames are
retained at the endpoint, not executed or assumed safe. -/
theorem LocalApplicationReturnBodyEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | application child =>
      cases evaluation with
      | application actual => exact actual.toStepsWithContinuation child sameIds continuation

/-- Reflection compares exact costs only at a genuinely final closed endpoint. -/
theorem LocalApplicationReturnBodyElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalApplicationReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  cases elaboration with
  | application child =>
      constructor
      · intro evaluation
        cases evaluation with
        | application actual => exact (child.evaluatesWithCost_iff_steps sameIds).mp actual
      · intro path
        exact .application ((child.evaluatesWithCost_iff_steps sameIds).mpr path)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationReturnBodyProperties`
-/

/-! Exact static provenance for one original application return. The body
retains its child's Core and type; no runtime value or store premise is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalApplicationReturnBodyElaborates.complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    elaborateLocalApplicationReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | application child => exact child.complete

theorem elaborateLocalApplicationReturnBody?_sound
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalApplicationReturnBody? table context body = some (core, type)) :
    LocalApplicationReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => cases accepted
  | cons statement rest =>
      rcases statement with ⟨returnSpan, payload⟩
      cases payload <;> try cases accepted
      case returnStmt returned =>
        cases returned with
        | none => cases accepted
        | some source =>
            cases rest with
            | cons _ _ => cases accepted
            | nil => exact .application (elaborateLocalFunctionApplication?_sound accepted)

theorem elaborateLocalApplicationReturnBody?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationReturnBody? table context body = some (core, type) ↔
      LocalApplicationReturnBodyElaborates table context body core type :=
  ⟨elaborateLocalApplicationReturnBody?_sound, LocalApplicationReturnBodyElaborates.complete⟩

theorem LocalApplicationReturnBodyElaborates.hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    LocalApplicationReturnBodyHasType table context body type := by
  cases elaboration with
  | application child => exact .application child.hasType

theorem LocalApplicationReturnBodyHasType.elaborates_exact
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : LocalApplicationReturnBodyHasType table context body type) :
    ∃ core, LocalApplicationReturnBodyElaborates table context body core type := by
  cases typing with
  | application child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .application elaboration⟩

theorem localApplicationReturnBodyHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} :
    LocalApplicationReturnBodyHasType table context body type ↔
      ∃ core, LocalApplicationReturnBodyElaborates table context body core type :=
  ⟨LocalApplicationReturnBodyHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem LocalApplicationReturnBodyElaborates.result_unique
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : LocalApplicationReturnBodyElaborates table context body leftCore leftType)
    (right : LocalApplicationReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType := by
  cases left with
  | application leftChild =>
      cases right with
      | application rightChild => exact leftChild.result_unique rightChild

theorem LocalApplicationReturnBodyHasType.type_unique
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (leftTyped : LocalApplicationReturnBodyHasType table context body left)
    (rightTyped : LocalApplicationReturnBodyHasType table context body right) : left = right := by
  cases leftTyped with
  | application leftChild =>
      cases rightTyped with
      | application rightChild => exact leftChild.type_unique rightChild

theorem LocalApplicationReturnBodyElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaboration with
  | application child => exact child.core_hasType

theorem elaborateLocalApplicationReturnBody?_core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalApplicationReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type :=
  (elaborateLocalApplicationReturnBody?_sound accepted).core_hasType

theorem elaborateLocalApplicationReturnBody?_eq_none_iff
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} :
    elaborateLocalApplicationReturnBody? table context body = none ↔
      ¬ ∃ type, LocalApplicationReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨_, typing⟩
    obtain ⟨_, elaboration⟩ := typing.elaborates_exact
    have accepted := elaboration.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalApplicationReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, (elaborateLocalApplicationReturnBody?_sound result).hasType⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationReturnBodyRunnerProperties`
-/

/-! Singleton wrapping preserves the child's entire checked result at every
fuel and store. Runtime-world and saved-state laws can be reused through this
equality without rebuilding inputs, frames, captures or stores. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkApplicationReturnBody?_return (inputs : LocalInputs)
    (blockSpan returnSpan : Syntax.SourceSpan) (source : Syntax.Expr) :
    inputs.checkApplicationReturnBody? ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ =
      inputs.checkApplication? source := rfl

theorem runApplicationReturnBody?_return (inputs : LocalInputs) (fuel : Nat)
    (blockSpan returnSpan : Syntax.SourceSpan) (source : Syntax.Expr) (store : Core.Store) :
    inputs.runApplicationReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ store =
      inputs.runApplication? fuel source store := rfl

theorem checkApplicationReturnBody?_iff_elaborates
    {inputs : LocalInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    inputs.checkApplicationReturnBody? body = some (core, type) ↔
      LocalApplicationReturnBodyElaborates inputs.names inputs.context body core type :=
  elaborateLocalApplicationReturnBody?_iff

theorem runApplicationReturnBody?_eq_some_iff
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runApplicationReturnBody? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkApplicationReturnBody? body = some (core, type) ∧
        Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runApplicationReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, same⟩
    exact ⟨(core, type), checked, by simp only [same]⟩

theorem runApplicationReturnBody?_eq_none_iff
    {inputs : LocalInputs} {body : Syntax.Block} (fuel : Nat) (store : Core.Store) :
    inputs.runApplicationReturnBody? fuel body store = none ↔
      inputs.checkApplicationReturnBody? body = none := by
  cases checked : inputs.checkApplicationReturnBody? body with
  | none => simp [runApplicationReturnBody?, checked]
  | some pair => cases pair; simp [runApplicationReturnBody?, checked]

/-- Fixed-fuel completion requires whole-body typing and an actual successful
cost within that fuel. Raw selected-path success alone does not open the gate. -/
theorem runApplicationReturnBody?_done_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    inputs.runApplicationReturnBody? fuel body initialStore = some (type, .done value finalStore) ↔
      LocalApplicationReturnBodyHasType inputs.names inputs.context body type ∧
        ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment
          initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro done
    obtain ⟨core, checked, execution⟩ := runApplicationReturnBody?_eq_some_iff.mp done
    have elaboration := checkApplicationReturnBody?_iff_elaborates.mp checked
    obtain ⟨cost, enough, path⟩ := Core.runStateful_sound execution
    exact ⟨elaboration.hasType, cost,
      (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr path, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    have path := evaluation.toStepsWithContinuation elaboration inputs.sameIds []
    exact runApplicationReturnBody?_eq_some_iff.mpr
      ⟨core, checkApplicationReturnBody?_iff_elaborates.mpr elaboration,
        path.runStateful_done_iff.mpr enough⟩

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithExpectedLambda`
-/

/-!
One opt-in singleton-application entry selects direct expected-lambda checking
or unchanged ordinary recursive checking solely from the original source shape.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly a singleton call whose sole argument is a direct lambda. -/
def isDirectExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .lambda _ _ _ _⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence for the expected-lambda and ordinary application
paths. Both constructors retain the complete original singleton call. -/
inductive LocalApplicationWithExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | expected {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isDirectExpectedLambdaArgumentApplication source = true)
      (elaboration : ExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type
  | ordinary {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {core : Core.Expr} {type : Core.Ty}
      (boundary : isDirectExpectedLambdaArgumentApplication
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = false)
      (elaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ core type) :
      LocalApplicationWithExpectedLambdaElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ core type

/-- Dispatch before checking. Failure in the recognized lambda branch never
falls through to the ordinary recursive checker. -/
def elaborateLocalApplicationWithExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call _ ⟨_, [_]⟩⟩ =>
      if isDirectExpectedLambdaArgumentApplication source then
        elaborateExpectedLambdaArgumentApplication? types owner inputs source
      else elaborateRecursiveLocalComputation? inputs.names inputs.context source
  | _ => none

/-- Exact correspondence for source-only disjoint dispatch. -/
theorem elaborateLocalApplicationWithExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = some (core, type) ↔
      LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateLocalApplicationWithExpectedLambda?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateLocalApplicationWithExpectedLambda?] at accepted
          | cons argument tail =>
            cases tail with
            | cons second rest => simp [elaborateLocalApplicationWithExpectedLambda?] at accepted
            | nil =>
              simp only [elaborateLocalApplicationWithExpectedLambda?] at accepted
              split at accepted
              · rename_i boundary
                exact .expected boundary
                  (elaborateExpectedLambdaArgumentApplication?_iff.mp accepted)
              · rename_i boundary
                have boundaryFalse : isDirectExpectedLambdaArgumentApplication
                    ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = false := by
                  cases equality : isDirectExpectedLambdaArgumentApplication
                      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ <;> simp_all
                exact .ordinary boundaryFalse
                  (elaborateRecursiveLocalComputation?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | expected boundary elaboration =>
        cases elaboration with
        | application calleeElaboration argumentElaboration =>
          simp [elaborateLocalApplicationWithExpectedLambda?, boundary,
            elaborateExpectedLambdaArgumentApplication?_iff.mpr
              (.application calleeElaboration argumentElaboration)]
    | ordinary boundary elaboration =>
        simp [elaborateLocalApplicationWithExpectedLambda?, boundary,
          elaborateRecursiveLocalComputation?_iff.mpr elaboration]

/-- Rejection is exact absence of both source-disjoint application paths. -/
theorem elaborateLocalApplicationWithExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateLocalApplicationWithExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithExpectedLambda? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithExpectedLambda?_iff.mp accepted⟩)

/-- Either selected path preserves the exact inferred Core type. -/
theorem LocalApplicationWithExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | expected boundary child => exact child.core_hasType
  | ordinary boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithExpectedLambdaElaborates
      types owner inputs source core type) :
    (isDirectExpectedLambdaArgumentApplication source = true ∧
      ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type) ∨
    (isDirectExpectedLambdaArgumentApplication source = false ∧
      ∃ span argumentsSpan callee argument,
        source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
        RecursiveLocalComputationElaborates inputs.names inputs.context source core type) := by
  cases elaboration with
  | expected boundary child => exact .inl ⟨boundary, child⟩
  | ordinary boundary child => exact .inr ⟨boundary, _, _, _, _, rfl, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithGroupedExpectedLambda`
-/

/-!
One opt-in group-first entry adds the one-level grouped expected-lambda path in
front of the unchanged direct-or-ordinary local-application entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly one grouped direct lambda as the sole call argument. -/
def isOneLevelGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence retains the complete grouped child or the complete
unchanged ADR-0318 child. -/
inductive LocalApplicationWithGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | grouped {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : GroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch on grouped source shape before entering the unchanged ADR-0318 entry. -/
def elaborateLocalApplicationWithGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isOneLevelGroupedExpectedLambdaArgumentApplication source then
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithExpectedLambda? types owner inputs source

/-- A recognized grouped source invokes only the ADR-0319 checker. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source := by
  simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary]

/-- Every other source has exactly the unchanged ADR-0318 checker result. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs source := by
  simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for group-first dispatch. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
        some (core, type) ↔
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .grouped boundary
        (elaborateGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundary
      have boundaryFalse :
          isOneLevelGroupedExpectedLambdaArgumentApplication source = false := by
        cases equality : isOneLevelGroupedExpectedLambdaArgumentApplication source <;>
          simp_all
      exact .existing boundaryFalse
        (elaborateLocalApplicationWithExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | grouped boundary child =>
        simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary,
          elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithGroupedExpectedLambda?, boundary,
          elaborateLocalApplicationWithExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of either selected application path. -/
theorem elaborateLocalApplicationWithGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none ↔
      ¬ ∃ core type, LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp accepted⟩)

/-- Either selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | grouped boundary child => exact child.core_hasType
  | existing boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    (isOneLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      GroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isOneLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | grouped boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithTwoLevelGroupedExpectedLambda`
-/

/-!
One opt-in exact-depth-two-first entry adds the two-level grouped
expected-lambda path in front of the unchanged ADR-0320 entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly a singleton call whose argument has two groups followed
immediately by a direct lambda. -/
def isTwoLevelGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence retains either the exact ADR0321 child or the
complete unchanged ADR0320 child. -/
inductive LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | twoLevel {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch on the exact-depth-two source shape before entering ADR0320. -/
def elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isTwoLevelGroupedExpectedLambdaArgumentApplication source then
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source

/-- A recognized exact-depth-two source invokes only ADR0321. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary]

/-- Every other source has exactly the unchanged ADR0320 result. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
      elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for exact-depth-two-first dispatch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .twoLevel boundary
        (elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundary
      have boundaryFalse :
          isTwoLevelGroupedExpectedLambdaArgumentApplication source = false := by
        cases equality : isTwoLevelGroupedExpectedLambdaArgumentApplication source <;>
          simp_all
      exact .existing boundaryFalse
        (elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | twoLevel boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary,
          elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?, boundary,
          elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type, LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mp accepted⟩)

/-- Either selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | twoLevel boundary child => exact child.core_hasType
  | existing boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
      types owner inputs source core type) :
    (isTwoLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithGroupedExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | twoLevel boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithConditionalAndFiniteGroupedExpectedLambda`
-/

/-!
One source-only conditional-first entry adds ADR-0324 and ADR-0323 before the
complete unchanged ADR-0322 local-application entry.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Three source-disjoint paths retain the complete selected child. -/
inductive LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | conditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | threeOrMoreGrouped {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = false)
      (groupedBoundary :
        isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true)
      (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (conditionalBoundary :
        isConditionalExpectedLambdaArgumentApplication source = false)
      (groupedBoundary :
        isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch only from the unchanged original source. Selected failure is final. -/
def elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isConditionalExpectedLambdaArgumentApplication source then
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs source
  else if isThreeOrMoreGroupedExpectedLambdaArgumentApplication source then
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source
  else elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
    types owner inputs source

/-- A recognized conditional invokes exactly ADR-0324. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_conditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary : isConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?, boundary]

/-- A nonconditional finite spine invokes exactly ADR-0323. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_threeOrMoreGrouped
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (conditionalBoundary :
      isConditionalExpectedLambdaArgumentApplication source = false)
    (groupedBoundary :
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
    conditionalBoundary, groupedBoundary]

/-- Every doubly unrecognized source has exactly the frozen ADR-0322 result. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (conditionalBoundary :
      isConditionalExpectedLambdaArgumentApplication source = false)
    (groupedBoundary :
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
    conditionalBoundary, groupedBoundary]

/-- Exact executable/declarative correspondence for conditional-first dispatch. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? at accepted
    split at accepted
    · rename_i conditionalBoundary
      exact .conditional conditionalBoundary
        (elaborateConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i conditionalNot
      have conditionalBoundary :
          isConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality : isConditionalExpectedLambdaArgumentApplication source <;> simp_all
      split at accepted
      · rename_i groupedBoundary
        exact .threeOrMoreGrouped conditionalBoundary groupedBoundary
          (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mp accepted)
      · rename_i groupedNot
        have groupedBoundary :
            isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false := by
          cases equality :
              isThreeOrMoreGroupedExpectedLambdaArgumentApplication source <;> simp_all
        exact .existing conditionalBoundary groupedBoundary
          (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | conditional boundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?, boundary,
          elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | threeOrMoreGrouped conditionalBoundary groupedBoundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
          conditionalBoundary, groupedBoundary,
          elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing conditionalBoundary groupedBoundary child =>
        simp [elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?,
          conditionalBoundary, groupedBoundary,
          elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source path. -/
theorem elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
          types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mp
          accepted⟩)

/-- Every selected child preserves its exact inferred Core type. -/
theorem LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | conditional _ child => exact child.core_hasType
  | threeOrMoreGrouped _ _ child => exact child.core_hasType
  | existing _ _ child => exact child.core_hasType

/-- Inversion exposes the ordered source partition and complete selected child. -/
theorem LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration :
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
    (isConditionalExpectedLambdaArgumentApplication source = true ∧
      ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isConditionalExpectedLambdaArgumentApplication source = false ∧
      ((isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true ∧
        ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
          types owner inputs source core type) ∨
       (isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false ∧
        LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
          types owner inputs source core type))) := by
  cases elaboration with
  | conditional boundary child => exact .inl ⟨boundary, child⟩
  | threeOrMoreGrouped conditionalBoundary groupedBoundary child =>
      exact .inr ⟨conditionalBoundary, .inl ⟨groupedBoundary, child⟩⟩
  | existing conditionalBoundary groupedBoundary child =>
      exact .inr ⟨conditionalBoundary, .inr ⟨groupedBoundary, child⟩⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithOneLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects ADR-0326 one-level grouped conditional applications before the exact
complete ADR-0325 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0326 child or the
complete unchanged ADR-0325 child. -/
inductive LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | oneLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0326 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    types owner inputs source

/-- A recognized one-level grouped conditional invokes exactly ADR-0326. -/
theorem elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0325 result. -/
theorem elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for grouped-conditional-first dispatch. -/
theorem elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .oneLevelGroupedConditional boundary
        (elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | oneLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | oneLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | oneLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithTwoLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0328 two-level grouped conditional application before
the complete unchanged ADR-0327 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0328 child or the
complete unchanged ADR-0327 child. -/
inductive LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | twoLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0328 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized two-level grouped conditional invokes exactly ADR-0328. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0327 result. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for two-level-first dispatch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .twoLevelGroupedConditional boundary
        (elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | twoLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | twoLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | twoLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithThreeLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0330 three-level grouped conditional application before
the complete unchanged ADR-0329 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0330 child or the
complete unchanged ADR-0329 child. -/
inductive LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | threeLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0330 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized three-level grouped conditional invokes exactly ADR-0330. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0329 result. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for three-level-first dispatch. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .threeLevelGroupedConditional boundary
        (elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | threeLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | threeLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | threeLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithFourLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0332 four-level grouped conditional application before
the complete unchanged ADR-0331 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0332 child or the
complete unchanged ADR-0331 child. -/
inductive LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | fourLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0332 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized four-level grouped conditional invokes exactly ADR-0332. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0331 result. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for four-level-first dispatch. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .fourLevelGroupedConditional boundary
        (elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | fourLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | fourLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | fourLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithFiveLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0334 five-level grouped conditional application before
the complete unchanged ADR-0333 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0334 child or the
complete unchanged ADR-0333 child. -/
inductive LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | fiveLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0334 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized five-level grouped conditional invokes exactly ADR-0334. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0333 result. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for five-level-first dispatch. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .fiveLevelGroupedConditional boundary
        (elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | fiveLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | fiveLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | fiveLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithSixLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0336 six-level grouped conditional application before
the complete unchanged ADR-0335 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0336 child or the
complete unchanged ADR-0335 child. -/
inductive LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | sixLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0336 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized six-level grouped conditional invokes exactly ADR-0336. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0335 result. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for six-level-first dispatch. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .sixLevelGroupedConditional boundary
        (elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | sixLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | sixLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | sixLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithSevenLevelGroupedConditionalExpectedLambda`
-/

/-!
Selects the exact ADR-0338 seven-level grouped conditional application before
the complete unchanged ADR-0337 local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the exact ADR-0338 child or the
complete unchanged ADR-0337 child. -/
inductive LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | sevenLevelGroupedConditional {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the unchanged ADR-0338 classifier. Selected failure is final. -/
def elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized seven-level grouped conditional invokes exactly ADR-0338. -/
theorem elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete unchanged ADR-0337 result. -/
theorem elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for seven-level-first dispatch. -/
theorem elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .sevenLevelGroupedConditional boundary
        (elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted)
    · rename_i boundaryNot
      have boundary :
          isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | sevenLevelGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | sevenLevelGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | sevenLevelGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalApplicationWithGenericGroupedConditionalExpectedLambda`
-/

/-!
Selects every depth-eight-or-more grouped conditional application before the
complete unchanged seven-level-first local-application result.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source-disjoint evidence retains either the generic grouped-conditional
child or the complete unchanged depth-zero-through-seven child. -/
inductive LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | eightOrMoreGroupedConditional
      {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true)
      (elaboration :
        EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
          types owner inputs source core type) :
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type
  | existing {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary :
        isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = false)
      (elaboration : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) :
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type

/-- Dispatch once on the generic classifier. Classifier-selected failure is final. -/
def elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source then
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source
  else elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
    types owner inputs source

/-- A recognized depth-eight-or-more grouped conditional invokes exactly the
generic adapter. -/
theorem elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true) :
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?, boundary]

/-- Every other source has exactly the complete depth-zero-through-seven result. -/
theorem elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_existing
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr}
    (boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = false) :
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
        types owner inputs source =
      elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
        types owner inputs source := by
  simp [elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?, boundary]

/-- Exact executable/declarative correspondence for generic-first dispatch. -/
theorem elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
        types owner inputs source = some (core, type) ↔
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    unfold elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda? at accepted
    split at accepted
    · rename_i boundary
      exact .eightOrMoreGroupedConditional boundary
        (elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp
          accepted)
    · rename_i boundaryNot
      have boundary :
          isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = false := by
        cases equality :
            isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source <;> simp_all
      exact .existing boundary
        (elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | eightOrMoreGroupedConditional boundary child =>
        simp [elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?, boundary,
          elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child]
    | existing boundary child =>
        simp [elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?, boundary,
          elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr child]

/-- Rejection is exact absence of evidence in the selected source branch. -/
theorem elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mp
          accepted⟩)

/-- Either complete selected child preserves the exact inferred Core type. -/
theorem LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | eightOrMoreGroupedConditional _ child => exact child.core_hasType
  | existing _ child => exact child.core_hasType

/-- Inversion exposes the classifier equation and the complete selected child. -/
theorem LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core type) :
    (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) ∨
    (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core type) := by
  cases elaboration with
  | eightOrMoreGroupedConditional boundary child => exact .inl ⟨boundary, child⟩
  | existing boundary child => exact .inr ⟨boundary, child⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.RuntimeApplicationFunction
/-! Runtime application-function compilation, entry, and factorization. -/

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionCompilation`
-/

/-! Value-free compilation for a separate original application-return entry.
The existing output record is data only; this profile has its own provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : LocalApplicationReturnBodyElaborates compiled.inputs.names compiled.inputs.context
    declaration.value.body compiled.core compiled.returnType

def compileRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionCompilationProperties`
-/

/-! Exact value-free compilation belongs to this application-return profile.
The shared data record supplies no old compilation or runtime safety evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionCompiles.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    compileRuntimeApplicationFunction? types owner declaration = some compiled := by
  simp only [compileRuntimeApplicationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
    compilation.parameters.complete, compilation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem compileRuntimeApplicationFunction?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeApplicationFunction? types owner declaration = some compiled) :
    RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  simp only [compileRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
      elaborateLocalApplicationReturnBody?_sound body⟩
  next => cases result

theorem compileRuntimeApplicationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeApplicationFunction? types owner declaration = some compiled ↔
      RuntimeApplicationFunctionCompiles types owner declaration compiled :=
  ⟨compileRuntimeApplicationFunction?_sound, RuntimeApplicationFunctionCompiles.complete⟩

/-- Independent parameter identity and exact original body evidence determine
the entire record, not just a Core expression with the same result type. -/
theorem RuntimeApplicationFunctionCompiles.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeApplicationFunctionCompiles types owner declaration left)
    (second : RuntimeApplicationFunctionCompiles types owner declaration right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have sameInputs : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨sameCore, sameType⟩ := first.body.result_unique second.body
  cases sameCore
  cases sameType
  rfl

theorem compileRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl} :
    compileRuntimeApplicationFunction? types owner declaration = none ↔
      ¬ ∃ compiled, RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  constructor
  · intro rejected ⟨compiled, compilation⟩
    have accepted := compilation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : compileRuntimeApplicationFunction? types owner declaration with
    | none => rfl
    | some compiled => exact False.elim (missing ⟨compiled, compileRuntimeApplicationFunction?_sound accepted⟩)

/-- The exact output remains open in the original parameter context. No actual
arguments, world, store or execution guarantee follow from this static law. -/
theorem RuntimeApplicationFunctionCompiles.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    Core.HasType (Resolved.LocalScope.values compiled.inputs.context) compiled.core compiled.returnType :=
  compilation.body.core_hasType

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionEntry`
-/

/-! A separate explicit whole-function entry using the original actual typed
arguments. Header, parameter and exact body evidence belong to this profile,
not to the unchanged pure/recursive entry sharing the data-only output record. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : LocalApplicationReturnBodyElaborates prepared.inputs.names prepared.inputs.context
    declaration.value.body prepared.core prepared.returnType

def prepareRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

/-- Preserve faults and genuine exhaustion as present results. Structural
argument evidence does not validate the actual store or referenced locations. -/
def runRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeApplicationFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core (Resolved.LocalScope.values prepared.inputs.environment) store))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionEntryProperties`
-/

/-! Exact whole-entry preparation fixes the actual input record and original
body Core. Full execution equations do not assert safety for arbitrary stores. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionPrepares.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared := by
  simp only [prepareRuntimeApplicationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
    preparation.parameters.complete, preparation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem prepareRuntimeApplicationFunction?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared) :
    RuntimeApplicationFunctionPrepares types owner declaration arguments prepared := by
  simp only [prepareRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      bindRuntimeParameters?_sound parameters, elaborateLocalApplicationReturnBody?_sound body⟩
  next => cases result

theorem prepareRuntimeApplicationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeApplicationFunction? types owner declaration arguments = some prepared ↔
      RuntimeApplicationFunctionPrepares types owner declaration arguments prepared :=
  ⟨prepareRuntimeApplicationFunction?_sound, RuntimeApplicationFunctionPrepares.complete⟩

/-- Independent actual binding and exact body provenance determine every field. -/
theorem RuntimeApplicationFunctionPrepares.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : RuntimeApplicationFunctionPrepares types owner declaration arguments left)
    (second : RuntimeApplicationFunctionPrepares types owner declaration arguments right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem prepareRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} :
    prepareRuntimeApplicationFunction? types owner declaration arguments = none ↔
      ¬ ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro rejected ⟨prepared, preparation⟩
    have accepted := preparation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : prepareRuntimeApplicationFunction? types owner declaration arguments with
    | none => rfl
    | some prepared => exact False.elim (missing ⟨prepared, prepareRuntimeApplicationFunction?_sound accepted⟩)

theorem RuntimeApplicationFunctionPrepares.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    Core.HasType (Resolved.LocalScope.values prepared.inputs.context) prepared.core prepared.returnType :=
  preparation.body.core_hasType

theorem runRuntimeApplicationFunction?_eq_some_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store = some (type, result) ↔
      ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = type ∧ Core.runStateful fuel (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) store) = result := by
  simp only [runRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨prepared, accepted, same⟩
    cases same
    exact ⟨prepared, prepareRuntimeApplicationFunction?_iff.mp accepted, rfl, rfl⟩
  · rintro ⟨prepared, preparation, sameType, execution⟩
    exact ⟨prepared, preparation.complete, by simp only [sameType, execution]⟩

theorem runRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store = none ↔
      prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
  cases prepared : prepareRuntimeApplicationFunction? types owner declaration arguments with
  | none => simp [runRuntimeApplicationFunction?, prepared]
  | some result => simp [runRuntimeApplicationFunction?, prepared]

/-- The whole original contract transports every body outcome unchanged,
including faults and the complete state of genuine exhaustion. -/
theorem RuntimeApplicationFunctionPrepares.run_eq_body
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store =
      prepared.inputs.runApplicationReturnBody? fuel declaration.value.body store := by
  simp only [runRuntimeApplicationFunction?, preparation.complete,
    LocalInputs.runApplicationReturnBody?, LocalInputs.checkApplicationReturnBody?,
    preparation.body.complete, bind, Option.bind_some, pure]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties`
-/

/-! New whole-entry provenance factors through original static parameters and
the actual supplied arguments. Reusing the data projection does not reuse the
old body's safety, store or fuel contracts. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionPrepares.compiles
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeApplicationFunctionPrepares types owner declaration arguments prepared) :
    RuntimeApplicationFunctionCompiles types owner declaration prepared.toCompiled := by
  refine ⟨preparation.header, preparation.parameters.erase_values, ?_⟩
  simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_names,
    LocalInputs.toTypeInputs_context] using preparation.body

theorem RuntimeApplicationFunctionCompiles.prepare_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse) :
    ∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matchingTypes
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩, ⟨compilation.header, bound, ?_⟩, ?_⟩
  · change LocalApplicationReturnBodyElaborates inputs.names inputs.context
      declaration.value.body compiled.core compiled.returnType
    rw [← LocalInputs.toTypeInputs_names inputs, ← LocalInputs.toTypeInputs_context inputs, erased]
    exact compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

theorem runtimeApplicationFunctionPrepares_toCompiled_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, RuntimeApplicationFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
      RuntimeApplicationFunctionCompiles types owner declaration compiled ∧
        arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse := by
  constructor
  · rintro ⟨prepared, preparation, rfl⟩
    refine ⟨preparation.compiles, ?_⟩
    have layout := congrArg List.reverse preparation.parameters.argument_types.symm
    simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
      Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
      List.map_reverse, List.reverse_reverse] using layout
  · rintro ⟨compilation, matchingTypes⟩
    exact compilation.prepare_arguments arguments matchingTypes

/-- Include every failure and the original ordered argument-type guard. -/
theorem prepareRuntimeApplicationFunction?_factorization
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeApplicationFunction? types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileRuntimeApplicationFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some compiled
        else none) := by
  cases compiledResult : compileRuntimeApplicationFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
        apply prepareRuntimeApplicationFunction?_eq_none_iff.mpr
        rintro ⟨prepared, preparation⟩
        have accepted := preparation.compiles.complete
        rw [compiledResult] at accepted
        cases accepted
      simp only [rejected, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeApplicationFunction?_sound compiledResult
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matching
        simp only [preparation.complete, Option.map_some, erased, bind, Option.bind_some,
          matching, ↓reduceIte]
      · have rejected : prepareRuntimeApplicationFunction? types owner declaration arguments = none := by
          apply prepareRuntimeApplicationFunction?_eq_none_iff.mpr
          rintro ⟨prepared, preparation⟩
          have erased := preparation.compiles.result_unique compilation
          exact matching (runtimeApplicationFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩).2
        simp only [rejected, Option.map_none, bind, Option.bind_some, matching, ↓reduceIte]

/-- The guard supplies actual values in source order; binding reverses them
once. This equality retains all outcomes and the supplied store, not just done. -/
theorem RuntimeApplicationFunctionCompiles.run_eq
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeApplicationFunction? types owner declaration arguments fuel store =
      some (compiled.returnType, Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store)) := by
  obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matchingTypes
  have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
  have returnEq : prepared.returnType = compiled.returnType := congrArg CompiledRuntimeFunction.returnType erased
  have valuesEq : Resolved.LocalScope.values prepared.inputs.environment = arguments.reverse.map (·.value) := by
    simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map, Function.comp_def]
      using preparation.parameters.argument_values
  simp only [runRuntimeApplicationFunction?, preparation.complete, bind, Option.bind_some, pure,
    coreEq, returnEq, valuesEq]

end Solcore.Frontend
end
