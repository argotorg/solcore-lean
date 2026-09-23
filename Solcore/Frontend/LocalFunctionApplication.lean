import Solcore.Frontend.LocalExpressionTyping
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Core.LocalFragment
import Solcore.Resolved.Eval
import Solcore.Core.Safety
import Solcore.Core.Correspondence
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.LocalReference
import Solcore.Resolved.Typing
import Solcore.Resolved.FreshIdentity
import Solcore.Resolved.LocalScope
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.LocalName
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Resolved.Scope
import Solcore.Resolved.Renaming
import Solcore.Frontend.LocalExpressionRenaming
import Solcore.Frontend.LocalTypeInputs
import Solcore.Core.Machine
import Solcore.Core.Derived
import Solcore.Core.FuelResumptionProperties

/-! An opt-in root application of a known single-argument Function. Both
original children use the old pure local profile. This does not extend that
profile, resolve general Invokable instances or integrate function entries. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Preserve the unique argument as written, without packing or an implicit
Unit. Failure is outside this adapter, not rejection by the full language. -/
def elaborateLocalFunctionApplication? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source.value with
  | .call callee ⟨_, [argument]⟩ => do
      let (functionCore, functionType) ← elaborateLocalExpression? table context callee
      let (argumentCore, argumentType) ← elaborateLocalExpression? table context argument
      match functionType with
      | .function parameterType resultType =>
          if argumentType = parameterType then
            some (.apply functionCore argumentCore, resultType)
          else none
      | _ => none
  | _ => none

/-- Whole static typing checks both original children in the same scope. -/
inductive LocalFunctionApplicationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | call {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty}
      (functionTyped : LocalExpressionHasType table context callee (.function parameterType resultType))
      (argumentTyped : LocalExpressionHasType table context argument parameterType) :
      LocalFunctionApplicationHasType table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ resultType

/-- Exact provenance fixes both resolved children and their positional Core,
separately from their types. No runtime values or executable checks are premises. -/
inductive LocalFunctionApplicationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | call {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {resolvedFunction resolvedArgument : Resolved.Expr} {functionCore argumentCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (functionResolution : ResolvesLocalExpression table callee resolvedFunction)
      (functionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedFunction functionCore)
      (functionTyped : Resolved.HasType context resolvedFunction (.function parameterType resultType))
      (argumentResolution : ResolvesLocalExpression table argument resolvedArgument)
      (argumentLowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedArgument argumentCore)
      (argumentTyped : Resolved.HasType context resolvedArgument parameterType) :
      LocalFunctionApplicationElaborates table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ (.apply functionCore argumentCore) resultType

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationInsertionProperties`
-/

/-! Exact application provenance supplies its two local child fragments.
Insertion changes only caller positions, not actual closure bodies or captures.
The arbitrary runtime environment and typing context need not match the source. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.core_evaluates_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (core.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore core value finalStore := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply
              ((functionLowered.localFragment.evaluates_insert_iff leading suffix inserted).mp functionEvaluation)
              ((argumentLowered.localFragment.evaluates_insert_iff leading suffix inserted).mp argumentEvaluation)
              bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply
              ((functionLowered.localFragment.evaluates_insert_iff leading suffix inserted).mpr functionEvaluation)
              ((argumentLowered.localFragment.evaluates_insert_iff leading suffix inserted).mpr argumentEvaluation)
              bodyEvaluation

theorem LocalFunctionApplicationElaborates.core_hasType_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Context) (inserted : Core.Ty)
    {requestedType : Core.Ty} {definitions : Core.DataEnvironment} :
    Core.HasType (leading ++ inserted :: suffix) (core.weakenAt leading.length) requestedType definitions ↔
      Core.HasType (leading ++ suffix) core requestedType definitions := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | apply functionTyping argumentTyping =>
            exact .apply
              ((functionLowered.localFragment.hasType_insert_iff leading suffix inserted).mp functionTyping)
              ((argumentLowered.localFragment.hasType_insert_iff leading suffix inserted).mp argumentTyping)
      · intro typing
        cases typing with
        | apply functionTyping argumentTyping =>
            exact .apply
              ((functionLowered.localFragment.hasType_insert_iff leading suffix inserted).mpr functionTyping)
              ((argumentLowered.localFragment.hasType_insert_iff leading suffix inserted).mpr argumentTyping)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationProperties`
-/

/-! Exact static correspondence for one known Function application. Actual
closures, their stores and their body costs are separate dynamic obligations. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Both original children check in the same scope; the result is their ordered
application, not an arbitrary replacement with the same type. -/
theorem elaborateLocalFunctionApplication?_children {table : LocalNameTable}
    {context : Resolved.Context} {span argumentsSpan : Syntax.SourceSpan}
    {callee argument : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalFunctionApplication? table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (core, type) ↔
      ∃ functionCore argumentCore parameterType,
        elaborateLocalExpression? table context callee = some (functionCore, .function parameterType type) ∧
        elaborateLocalExpression? table context argument = some (argumentCore, parameterType) ∧
        core = .apply functionCore argumentCore := by
  simp only [elaborateLocalFunctionApplication?, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨functionCore, functionType⟩, functionAccepted,
      ⟨argumentCore, argumentType⟩, argumentAccepted, result⟩
    cases functionType <;> try cases result
    case function parameterType resultType =>
      dsimp only at result
      split at result
      next same =>
        cases result
        exact ⟨functionCore, argumentCore, parameterType, functionAccepted, same ▸ argumentAccepted, rfl⟩
      next => cases result
  · rintro ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩
    exact ⟨(functionCore, .function parameterType type), functionAccepted,
      (argumentCore, parameterType), argumentAccepted, by simp⟩

theorem LocalFunctionApplicationElaborates.complete {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    elaborateLocalFunctionApplication? table context source = some (core, type) := by
  cases elaboration with
  | call functionResolution functionLowered functionTyped argumentResolution argumentLowered argumentTyped =>
      exact elaborateLocalFunctionApplication?_children.mpr ⟨_, _, _,
        elaborateLocalExpression?_complete functionResolution functionLowered functionTyped,
        elaborateLocalExpression?_complete argumentResolution argumentLowered argumentTyped, rfl⟩

theorem elaborateLocalFunctionApplication?_sound {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type)) :
    LocalFunctionApplicationElaborates table context source core type := by
  rcases source with ⟨span, payload⟩
  cases payload <;> try cases accepted
  case call callee arguments =>
    rcases arguments with ⟨argumentsSpan, arguments⟩
    cases arguments with
    | nil => cases accepted
    | cons argument rest =>
        cases rest with
        | cons _ _ => cases accepted
        | nil =>
            obtain ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩ :=
              elaborateLocalFunctionApplication?_children.mp accepted
            obtain ⟨resolvedFunction, functionResolution, functionLowered, functionTyped⟩ :=
              elaborateLocalExpression?_sound functionAccepted
            obtain ⟨resolvedArgument, argumentResolution, argumentLowered, argumentTyped⟩ :=
              elaborateLocalExpression?_sound argumentAccepted
            exact .call functionResolution functionLowered functionTyped
              argumentResolution argumentLowered argumentTyped

theorem elaborateLocalFunctionApplication?_iff {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalFunctionApplication? table context source = some (core, type) ↔
      LocalFunctionApplicationElaborates table context source core type :=
  ⟨elaborateLocalFunctionApplication?_sound, LocalFunctionApplicationElaborates.complete⟩

theorem LocalFunctionApplicationElaborates.hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    LocalFunctionApplicationHasType table context source type := by
  cases elaboration with
  | call functionResolution _ functionTyped argumentResolution _ argumentTyped =>
      exact .call (functionResolution.reflects_type functionTyped)
        (argumentResolution.reflects_type argumentTyped)

theorem LocalFunctionApplicationHasType.elaborates_exact {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType table context source type) :
    ∃ core, LocalFunctionApplicationElaborates table context source core type := by
  cases typing with
  | call functionTyped argumentTyped =>
      obtain ⟨resolvedFunction, functionResolution, functionTyping⟩ := functionTyped.resolves
      obtain ⟨functionCore, functionLowered, _⟩ := functionTyping.lowers
      obtain ⟨resolvedArgument, argumentResolution, argumentTyping⟩ := argumentTyped.resolves
      obtain ⟨argumentCore, argumentLowered, _⟩ := argumentTyping.lowers
      exact ⟨.apply functionCore argumentCore, .call functionResolution functionLowered functionTyping
        argumentResolution argumentLowered argumentTyping⟩

theorem localFunctionApplicationHasType_iff_elaborates {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    LocalFunctionApplicationHasType table context source type ↔
      ∃ core, LocalFunctionApplicationElaborates table context source core type :=
  ⟨LocalFunctionApplicationHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem LocalFunctionApplicationElaborates.result_unique {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {leftCore rightCore : Core.Expr}
    {leftType rightType : Core.Ty}
    (left : LocalFunctionApplicationElaborates table context source leftCore leftType)
    (right : LocalFunctionApplicationElaborates table context source rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem LocalFunctionApplicationHasType.type_unique {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {left right : Core.Ty}
    (leftTyped : LocalFunctionApplicationHasType table context source left)
    (rightTyped : LocalFunctionApplicationHasType table context source right) : left = right := by
  obtain ⟨_, leftElaboration⟩ := leftTyped.elaborates_exact
  obtain ⟨_, rightElaboration⟩ := rightTyped.elaborates_exact
  exact (leftElaboration.result_unique rightElaboration).2

/-- Static typing requires no actual argument or closure inhabitants and adds
no claim about stores, runtime worlds, local-fragment membership or fuel. -/
theorem LocalFunctionApplicationElaborates.core_hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaboration with
  | call _ functionLowered functionTyped _ argumentLowered argumentTyped =>
      exact .apply (functionLowered.preserves_type functionTyped) (argumentLowered.preserves_type argumentTyped)

theorem elaborateLocalFunctionApplication?_core_hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type :=
  (elaborateLocalFunctionApplication?_sound accepted).core_hasType

theorem elaborateLocalFunctionApplication?_eq_none_iff {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} :
    elaborateLocalFunctionApplication? table context source = none ↔
      ¬ ∃ type, LocalFunctionApplicationHasType table context source type := by
  constructor
  · intro rejected ⟨_, typing⟩
    obtain ⟨_, elaboration⟩ := typing.elaborates_exact
    have accepted := elaboration.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalFunctionApplication? table context source with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, (elaborateLocalFunctionApplication?_sound result).hasType⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationRuntimeStateProperties`
-/

/-! Runtime-world safety for the exact original Core application. These
state-only results use positional values, not source lookup correspondence;
ordered ID alignment is therefore not a premise. All outer frames are typed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.runtime_state_hasType
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType) :
    Core.StateHasType
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ resultType :=
  .eval storeTyped environmentTyped elaboration.core_hasType continuationTyped

theorem LocalFunctionApplicationElaborates.runtime_run_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ ≠
      .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (elaboration.runtime_state_hasType environmentTyped storeTyped continuationTyped)

/-- The entire actually suspended state is retained, including its captured
values, frames and current store. Its typing may use an extended world. -/
theorem LocalFunctionApplicationElaborates.runtime_checkpoint_hasType
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ =
      .outOfFuel checkpoint) :
    Core.StateHasType checkpoint resultType :=
  (Core.runStateful_outOfFuel_sound exhausted).1.preserve_state_type
    (elaboration.runtime_state_hasType environmentTyped storeTyped continuationTyped)

theorem LocalFunctionApplicationElaborates.runtime_checkpoint_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store)
    {continuation : List Core.Frame} {resultType : Core.Ty}
    (continuationTyped : Core.ContinuationHasType world continuation type resultType)
    {spent : Nat} {checkpoint : Core.State}
    (exhausted : Core.runStateful spent
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩ =
      .outOfFuel checkpoint)
    (additional : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful additional checkpoint ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (elaboration.runtime_checkpoint_hasType environmentTyped storeTyped continuationTyped exhausted)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationStepComposition`
-/

/-! Exact application protocol for the actual closure and captured environment.
The known body cost is lifted unchanged; outer frames are retained, not run. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

private theorem transition_append {start finish : State}
    (step : Transition start finish) (continuation : List Frame) :
    Transition { start with continuation := start.continuation ++ continuation }
      { finish with continuation := finish.continuation ++ continuation } := by
  cases step <;> simp only [List.cons_append] <;> constructor <;> assumption

private theorem steps_append {cost : Nat} {start finish : State}
    (path : Steps cost start finish) (continuation : List Frame) :
    Steps cost { start with continuation := start.continuation ++ continuation }
      { finish with continuation := finish.continuation ++ continuation } := by
  induction path with
  | refl => exact .refl
  | cons step _ ih => exact .cons (transition_append step continuation) ih

/-- Evaluate the original function and argument in the caller environment,
then the actual body under the argument followed by its captured values.
The three added transitions neither inspect nor execute the outer continuation.
No typing, purity, store-invariance or termination premise is inferred. -/
theorem apply {environment capturedEnvironment : Environment}
    {initialStore argumentStore bodyStore finalStore : Store}
    {function argument body : Expr} {parameterType resultType : Ty}
    {argumentValue result : Value} {continuation : List Frame}
    {functionCost argumentCost bodyCost : Nat}
    (functionPath : Steps functionCost
      ⟨.eval function environment, .applyArgument argument environment :: continuation, initialStore⟩
      ⟨.ret (.closure parameterType resultType body capturedEnvironment),
        .applyArgument argument environment :: continuation, argumentStore⟩)
    (argumentPath : Steps argumentCost
      ⟨.eval argument environment,
        .applyClosure parameterType resultType body capturedEnvironment :: continuation, argumentStore⟩
      ⟨.ret argumentValue,
        .applyClosure parameterType resultType body capturedEnvironment :: continuation, bodyStore⟩)
    (bodyPath : Steps bodyCost
      (State.initial body (argumentValue :: capturedEnvironment) bodyStore)
      (State.final result finalStore)) :
    Steps (functionCost + argumentCost + bodyCost + 3)
      ⟨.eval (.apply function argument) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have lifted : Steps bodyCost
      ⟨.eval body (argumentValue :: capturedEnvironment), continuation, bodyStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
    simpa only [State.initial, State.final, List.nil_append] using steps_append bodyPath continuation
  have path := Steps.cons .enterApply
    (functionPath.trans (.cons .beginArgument (argumentPath.trans (.cons .invokeClosure lifted))))
  simpa only [Nat.add_assoc] using path

end Solcore.Frontend.CostStepComposition

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationInsertionPaths`
-/

/-! One caller insertion preserves the literal closure and argument returned
by the two local children. Both applications then invoke the same actual body
path and captures, choosing a common cost before the outer continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source provenance supplies child fragments, not a runtime context premise.
Each side retains its own caller frames; only the resulting value, store and
successful cost agree. The actual closure body need not be pure or typed. -/
theorem LocalFunctionApplicationElaborates.core_insertion_paths
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore core value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ :=
            functionLowered.localFragment.insertion_paths leading suffix inserted functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ :=
            argumentLowered.localFragment.insertion_paths leading suffix inserted argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationExactInsertionProperties`
-/

/-! Supplied closed paths keep their exact cost under caller insertion.
Only final paths identify costs; outer continuations are retained, not run. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.core_steps_insert
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value}
    (path : Core.Steps cost (Core.State.initial core (leading ++ suffix) initialStore)
      (Core.State.final value finalStore)) (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix),
        continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  obtain ⟨commonCost, paths⟩ := elaboration.core_insertion_paths leading suffix inserted
    (Core.steps_from_initial_sound path)
  have sameCost : cost = commonCost := (path.final_unique (paths []).1).1
  exact sameCost.symm ▸ (paths continuation).2

theorem LocalFunctionApplicationElaborates.core_steps_reflect_insert
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value}
    (path : Core.Steps cost
      (Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix)
        initialStore) (Core.State.final value finalStore)) (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have evaluation := (elaboration.core_evaluates_insert_iff leading suffix inserted).mp
    (Core.steps_from_initial_sound path)
  obtain ⟨commonCost, paths⟩ :=
    elaboration.core_insertion_paths leading suffix inserted evaluation
  have sameCost : cost = commonCost := (path.final_unique (paths []).2).1
  exact sameCost.symm ▸ (paths continuation).1

theorem LocalFunctionApplicationElaborates.core_steps_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {cost : Nat} {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Steps cost
      (Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix)
        initialStore) (Core.State.final value finalStore) ↔
    Core.Steps cost (Core.State.initial core (leading ++ suffix) initialStore)
      (Core.State.final value finalStore) :=
  ⟨fun path => elaboration.core_steps_reflect_insert leading suffix inserted path [],
    fun path => elaboration.core_steps_insert leading suffix inserted path []⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputs`
-/

/-! Explicit typed local inputs with unique assigned identities. All three
projections retain the same order; repeated spellings keep the existing
first-match table behavior. This does not introduce source binding syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One supplied local value with structural Core typing evidence. This does
not assert allocation or runtime store validity for a contained reference. -/
structure TypedLocalBinding where
  name : String
  id : Resolved.LocalId
  type : Core.Ty
  value : Core.Value
  valueTyped : Core.ValueHasType value type

/-- A shared ordered input for name resolution, checking, and execution.
Unique IDs prevent one spelling from selecting another row's type or value. -/
structure LocalInputs where
  bindings : List TypedLocalBinding
  ids_nodup : (bindings.map (·.id)).Nodup

namespace LocalInputs

def ids (inputs : LocalInputs) : List Resolved.LocalId :=
  inputs.bindings.map (·.id)

def names (inputs : LocalInputs) : LocalNameTable :=
  inputs.bindings.map fun binding => (binding.name, binding.id)

def context (inputs : LocalInputs) : Resolved.Context :=
  inputs.bindings.map fun binding => (binding.id, binding.type)

def environment (inputs : LocalInputs) : Resolved.Environment :=
  inputs.bindings.map fun binding => (binding.id, binding.value)

def empty : LocalInputs := ⟨[], by simp⟩

/-- Prepend one explicitly typed input using an ID fresh only for these
inputs. A repeated spelling shadows its previous table entry; this is not
a source-language allocation policy or an existing-source preservation law. -/
def bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) : LocalInputs where
  bindings := {
    name
    id := Resolved.freshLocalId owner inputs.ids
    type
    value
    valueTyped
  } :: inputs.bindings
  ids_nodup := by
    change (Resolved.freshLocalId owner inputs.ids :: inputs.ids).Nodup
    exact List.nodup_cons.mpr
      ⟨Resolved.freshLocalId_not_mem owner inputs.ids, inputs.ids_nodup⟩

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsApplication`
-/

/-! A separate checked application endpoint on the actual supplied input rows.
Check absence, runtime faults and fuel exhaustion remain distinct outcomes.
Structural input typing does not validate referenced cells or store payloads. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkApplication? (inputs : LocalInputs) (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  elaborateLocalFunctionApplication? inputs.names inputs.context source

/-- Preserve the checked type tag and complete actual Core result. Typed
runtime-world/store premises belong to safety theorems, not this executable gate. -/
def runApplication? (inputs : LocalInputs) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkApplication? source
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExecution`
-/

/-! A proof-carrying input boundary for checked local expression execution.
Check failure is absent; fuel exhaustion retains its present stateful result. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def check? (inputs : LocalInputs) (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  elaborateLocalExpression? inputs.names inputs.context source

/-- Execute the actual checked Core expression with its corresponding values.
No source-text parsing, external-value validation, or wire endpoint is added. -/
def run? (inputs : LocalInputs) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.check? source
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsLookupProperties`
-/

/-! Unique row identities keep selected names, types, and values aligned.
Membership alone selects an identity, not a spelling: repeated names still
obey the independent first-match name lookup judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem lookup_projected_of_mem {α : Type} (project : TypedLocalBinding → α)
    {bindings : List TypedLocalBinding} {binding : TypedLocalBinding}
    (unique : (bindings.map (·.id)).Nodup) (member : binding ∈ bindings) :
    Resolved.LocalScope.Lookup (bindings.map fun row => (row.id, project row))
      binding.id (project binding) := by
  induction bindings with
  | nil => cases member
  | cons head rest ih =>
      have uniqueParts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · subst head
        exact .head
      · have different : head.id ≠ binding.id := by
          intro same
          apply uniqueParts.1
          change head.id ∈ rest.map (·.id)
          rw [same]
          exact List.mem_map.mpr ⟨binding, member, rfl⟩
        exact .tail different (ih uniqueParts.2 member)

namespace LocalInputs

theorem context_lookup_of_mem (inputs : LocalInputs) {binding : TypedLocalBinding}
    (member : binding ∈ inputs.bindings) :
    Resolved.LocalScope.Lookup inputs.context binding.id binding.type :=
  lookup_projected_of_mem (·.type) inputs.ids_nodup member

theorem environment_lookup_of_mem (inputs : LocalInputs) {binding : TypedLocalBinding}
    (member : binding ∈ inputs.bindings) :
    Resolved.LocalScope.Lookup inputs.environment binding.id binding.value :=
  lookup_projected_of_mem (·.value) inputs.ids_nodup member

/-- A successful first-match name query identifies one actual row whose type
and value are selected by both identity projections. Later equal spellings
are not selected merely because they occur in the input list. -/
theorem lookup?_binding (inputs : LocalInputs) {spelling : String} {id : Resolved.LocalId}
    (selected : LocalNameTable.lookup? inputs.names spelling = some id) :
    ∃ binding, binding ∈ inputs.bindings ∧ binding.name = spelling ∧ binding.id = id ∧
      Resolved.LocalScope.Lookup inputs.context id binding.type ∧
      Resolved.LocalScope.Lookup inputs.environment id binding.value ∧
      Core.ValueHasType binding.value binding.type := by
  have namedMember := (LocalNameTable.lookup?_iff.mp selected).mem
  obtain ⟨binding, member, same⟩ := List.mem_map.mp namedMember
  have nameEq : binding.name = spelling := congrArg Prod.fst same
  have idEq : binding.id = id := congrArg Prod.snd same
  refine ⟨binding, member, nameEq, idEq, ?_, ?_, binding.valueTyped⟩
  · simpa only [idEq] using inputs.context_lookup_of_mem member
  · simpa only [idEq] using inputs.environment_lookup_of_mem member

/-- The newly prepended name and fresh identity select the same supplied type
and value, including when the spelling already occurs among older rows. -/
theorem bindFresh_lookups (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    LocalNameTable.Lookup (inputs.bindFresh owner name type value valueTyped).names
        name (Resolved.freshLocalId owner inputs.ids) ∧
      Resolved.LocalScope.Lookup (inputs.bindFresh owner name type value valueTyped).context
        (Resolved.freshLocalId owner inputs.ids) type ∧
      Resolved.LocalScope.Lookup (inputs.bindFresh owner name type value valueTyped).environment
        (Resolved.freshLocalId owner inputs.ids) value :=
  ⟨.head, .head, .head⟩

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsProperties`
-/

/-! Projection alignment and fresh-input construction are structural. These
laws require no caller-supplied synchronization of names, types, and values. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

@[simp] theorem context_ids (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.context = inputs.ids := by
  simp [context, ids, Resolved.LocalScope.ids, List.map_map]

@[simp] theorem environment_ids (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.environment = inputs.ids := by
  simp [environment, ids, Resolved.LocalScope.ids, List.map_map]

theorem sameIds (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.environment =
      Resolved.LocalScope.ids inputs.context :=
  (environment_ids inputs).trans (context_ids inputs).symm

theorem environmentTyped (inputs : LocalInputs) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values inputs.environment)
      (Resolved.LocalScope.values inputs.context) := by
  have typed : Core.EnvironmentHasTypes
      (inputs.bindings.map (·.value)) (inputs.bindings.map (·.type)) := by
    induction inputs.bindings with
    | nil => exact .nil
    | cons binding rest ih => exact .cons binding.valueTyped ih
  simpa [environment, context, Resolved.LocalScope.values, List.map_map, Function.comp_def] using typed

@[simp] theorem empty_ids : empty.ids = [] := rfl

@[simp] theorem empty_names : empty.names = [] := rfl

@[simp] theorem empty_context : empty.context = [] := rfl

@[simp] theorem empty_environment : empty.environment = [] := rfl

theorem bindFresh_bindings (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).bindings =
      { name, id := Resolved.freshLocalId owner inputs.ids, type, value, valueTyped } ::
        inputs.bindings := rfl

@[simp] theorem bindFresh_ids (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).ids =
      Resolved.freshLocalId owner inputs.ids :: inputs.ids := rfl

@[simp] theorem bindFresh_names (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).names =
      (name, Resolved.freshLocalId owner inputs.ids) :: inputs.names := rfl

@[simp] theorem bindFresh_context (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).context =
      (Resolved.freshLocalId owner inputs.ids, type) :: inputs.context := rfl

@[simp] theorem bindFresh_environment (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).environment =
      (Resolved.freshLocalId owner inputs.ids, value) :: inputs.environment := rfl

/-- Freshness is relative to the supplied inputs, not a global allocation claim. -/
theorem bindFresh_id_fresh (inputs : LocalInputs) (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner inputs.ids ∉ inputs.ids :=
  Resolved.freshLocalId_not_mem owner inputs.ids

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExecutionProperties`
-/

/-! Typed input projection discharges runtime identity alignment automatically.
Whole-expression typing remains essential to the checked evaluation boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem check?_iff_hasType {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty} :
    (∃ core, inputs.check? source = some (core, type)) ↔
      LocalExpressionHasType inputs.names inputs.context source type :=
  localExpressionHasType_iff_elaborates.symm

theorem run?_eq_some_iff {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.run? fuel source store = some (type, result) ↔
      ∃ core, inputs.check? source = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [run?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Absence is independent of fuel: it means no checked Core was produced. -/
theorem run?_eq_none_iff {inputs : LocalInputs} {source : Syntax.Expr} (fuel : Nat)
    (store : Core.Store) : inputs.run? fuel source store = none ↔ inputs.check? source = none := by
  cases checked : inputs.check? source with
  | none => simp [run?, checked]
  | some pair => cases pair; simp [run?, checked]

theorem run?_done_sound {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value}
    (result : inputs.run? fuel source initialStore = some (type, .done value finalStore)) :
    LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore ∧
      Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨core, checked, execution⟩ := run?_eq_some_iff.mp result
  obtain ⟨evaluation, storeEq⟩ := elaborateLocalExpression?_run_done_sound
    checked inputs.sameIds execution
  have typing := check?_iff_hasType.mp ⟨core, checked⟩
  exact ⟨evaluation, (evaluation.preserves_type typing inputs.sameIds inputs.environmentTyped).1, storeEq⟩

theorem typed_run_has_sufficient_fuel {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates inputs.names inputs.environment store source value store ∧
      Core.ValueHasType value type ∧
      ∀ fuel, required ≤ fuel → inputs.run? fuel source store = some (type, .done value store) := by
  obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
  obtain ⟨value, required, evaluation, valueTyped, enough⟩ :=
    elaborateLocalExpression?_typed_execution checked inputs.sameIds inputs.environmentTyped store
  exact ⟨value, required, evaluation, valueTyped, fun fuel bounded =>
    run?_eq_some_iff.mpr ⟨core, checked, enough fuel bounded⟩⟩

/-- The exact executable completion boundary includes source typing. Raw
selected-branch evaluation alone does not imply whole-expression checking. -/
theorem run?_done_iff_typed_evaluation {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, inputs.run? fuel source initialStore = some (type, .done value finalStore)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore := by
  constructor
  · rintro ⟨fuel, result⟩
    obtain ⟨core, checked, _⟩ := run?_eq_some_iff.mp result
    exact ⟨check?_iff_hasType.mp ⟨core, checked⟩, (run?_done_sound result).1⟩
  · rintro ⟨typing, evaluation⟩
    obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
    obtain ⟨fuel, execution⟩ := (elaborateLocalExpression?_evaluates_iff_run_done
      checked inputs.sameIds).mp evaluation
    exact ⟨fuel, run?_eq_some_iff.mpr ⟨core, checked, execution⟩⟩

/-- Any source either fails this checker or runs its typed pure Core. Even
at insufficient fuel, the convenience endpoint cannot return a machine fault. -/
theorem run?_never_faults (inputs : LocalInputs) (source : Syntax.Expr) (fuel : Nat)
    (store : Core.Store) (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.run? fuel source store ≠ some (type, .fault error faultState) := by
  intro result
  obtain ⟨core, checked, fault⟩ := run?_eq_some_iff.mp result
  exact elaborateLocalExpression?_run_never_faults checked inputs.sameIds inputs.environmentTyped
    store fuel error faultState fault

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExtensionLookupSupport`
-/

/-! Shared lookup facts for preserving source meaning when a fresh typed input
is added. Freshness is relative to the existing input rows, not global. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputExtensionSupport

theorem fresh_ne_of_named (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    {spelling : String} {id : Resolved.LocalId}
    (named : LocalNameTable.Lookup inputs.names spelling id) :
    Resolved.freshLocalId owner inputs.ids ≠ id := by
  obtain ⟨binding, member, _, idEq, _⟩ :=
    inputs.lookup?_binding (LocalNameTable.lookup?_iff.mpr named)
  intro same
  apply inputs.bindFresh_id_fresh owner
  exact List.mem_map.mpr ⟨binding, member, idEq.trans same.symm⟩

theorem identity_lookup_cons_iff {α : Type} {scope : Resolved.LocalScope α}
    {id newId : Resolved.LocalId} {value newValue : α} (different : newId ≠ id) :
    Resolved.LocalScope.Lookup ((newId, newValue) :: scope) id value ↔
      Resolved.LocalScope.Lookup scope id value := by
  constructor
  · intro found
    cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => exact found
  · exact Resolved.LocalScope.Lookup.tail different

end Solcore.Frontend.LocalInputExtensionSupport

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExtensionTyping`
-/

/-! Adding a differently named fresh typed input preserves and reflects source
typing. The supplied value does not change any existing identity lookup. -/

set_option autoImplicit false

namespace Solcore.Frontend

open LocalInputExtensionSupport

theorem AvoidsLocalName.bindFresh_hasType_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType) {resultType : Core.Ty} :
    LocalExpressionHasType (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).context source resultType ↔
      LocalExpressionHasType inputs.names inputs.context source resultType := by
  induction avoids generalizing resultType with
  | unit =>
      constructor <;> intro typing <;> cases typing <;> exact .unit
  | identifier different =>
      constructor
      · intro typing
        cases typing with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro typing
        cases typing with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | literal =>
      constructor
      · intro typing
        cases typing with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro typing
        cases typing with
        | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro typing
        cases typing with
        | group child => exact .group (ih.mp child)
      · intro typing
        cases typing with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | many _ _ headIH tailIH =>
      constructor
      · intro typing
        cases typing with
        | many head tail => exact .many (headIH.mp head) (tailIH.mp tail)
      · intro typing
        cases typing with
        | many head tail => exact .many (headIH.mpr head) (tailIH.mpr tail)
  | logicalNot _ ih =>
      constructor
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro typing
        cases typing with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro typing
        cases typing with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | logicalAnd left right => exact .logicalAnd (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | logicalAnd left right => exact .logicalAnd (leftIH.mpr left) (rightIH.mpr right)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro typing
        cases typing with
        | logicalOr left right => exact .logicalOr (leftIH.mp left) (rightIH.mp right)
      · intro typing
        cases typing with
        | logicalOr left right => exact .logicalOr (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mp condition) (thenIH.mp thenBranch) (elseIH.mp elseBranch)
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mpr condition) (thenIH.mpr thenBranch) (elseIH.mpr elseBranch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExtensionSemantics`
-/

/-! Adding a differently named fresh typed input preserves existing source
typing and evaluation. No source binding syntax or global allocation rule is
introduced; the exact value and both store endpoints are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

open LocalInputExtensionSupport

/-- Avoidance preserves and reflects raw source evaluation. Missing names in
an unselected branch need not resolve or type-check for this exact-store law. -/
theorem AvoidsLocalName.bindFresh_evaluates_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {result : Core.Value} :
    LocalExpressionEvaluates (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).environment
        initialStore source result finalStore ↔
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source result finalStore := by
  induction avoids generalizing initialStore finalStore result with
  | unit => constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | identifier different =>
      constructor
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | literal =>
      constructor
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | many _ _ headIH tailIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | many head tail => exact .many (headIH.mp head) (tailIH.mp tail)
      · intro evaluation
        cases evaluation with
        | many head tail => exact .many (headIH.mpr head) (tailIH.mpr tail)
  | logicalNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mp left) (rightIH.mp right)
        | andFalse left => exact .andFalse (leftIH.mp left)
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mpr left) (rightIH.mpr right)
        | andFalse left => exact .andFalse (leftIH.mpr left)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mp left)
        | orFalse left right => exact .orFalse (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mpr left)
        | orFalse left right => exact .orFalse (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mp condition) (thenIH.mp branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mp condition) (elseIH.mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mpr condition) (thenIH.mpr branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mpr condition) (elseIH.mpr branch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsExtensionProperties`
-/

/-! Unused-name insertion shifts free Core positions while preserving the
checked type, failure boundary, and completed value/store observations. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem AvoidsLocalName.check_bindFresh_complete {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {core : Core.Expr} {type : Core.Ty} (accepted : inputs.check? source = some (core, type)) :
    (inputs.bindFresh owner name newType newValue valueTyped).check? source =
      some (core.weakenAt 0, type) := by
  obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  have fresh : Resolved.freshLocalId owner inputs.ids ∉ Resolved.LocalScope.ids inputs.context := by
    simpa only [inputs.context_ids] using inputs.bindFresh_id_fresh owner
  exact elaborateLocalExpression?_complete
    (avoids.resolves_cons_iff.mpr resolution) (lowered.weaken_fresh fresh)
    (typing.weaken_fresh fresh newType)

/-- Exact checking agreement includes unresolved and ill-typed failures. Only
free Core indices shift; the source expression and assigned type are unchanged. -/
theorem AvoidsLocalName.check_bindFresh_eq {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType) :
    (inputs.bindFresh owner name newType newValue valueTyped).check? source =
      (inputs.check? source).map (fun result => (result.1.weakenAt 0, result.2)) := by
  cases accepted : inputs.check? source with
  | none =>
      have noOldType := elaborateLocalExpression?_eq_none_iff.mp accepted
      have newRejected : (inputs.bindFresh owner name newType newValue valueTyped).check? source = none :=
        elaborateLocalExpression?_eq_none_iff.mpr (by
          rintro ⟨type, typing⟩
          exact noOldType ⟨type,
            (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped).mp typing⟩)
      simpa only [Option.map_none] using newRejected
  | some result =>
      rcases result with ⟨core, type⟩
      exact avoids.check_bindFresh_complete inputs owner newType newValue valueTyped accepted

/-- Completed runs agree on type, value, and both stores. Fuel bounds may be
witnessed separately; this law does not equate suspended Core states. -/
theorem AvoidsLocalName.bindFresh_run_done_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source initialStore =
      some (type, .done value finalStore)) ↔
      ∃ fuel, inputs.run? fuel source initialStore = some (type, .done value finalStore) := by
  rw [LocalInputs.run?_done_iff_typed_evaluation, LocalInputs.run?_done_iff_typed_evaluation]
  exact and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped)
    (avoids.bindFresh_evaluates_iff inputs owner newType newValue valueTyped)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsRenaming`
-/

/-! Relabel explicit input identities without changing row order, spelling,
type, or value. Injectivity preserves the bundle's unique-ID invariant. -/

set_option autoImplicit false

namespace Solcore.Frontend

def TypedLocalBinding.mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (binding : TypedLocalBinding) : TypedLocalBinding :=
  { binding with id := mapping binding.id }

@[simp] theorem TypedLocalBinding.mapIds_id (binding : TypedLocalBinding) :
    binding.mapIds _root_.id = binding := by cases binding; rfl

theorem TypedLocalBinding.mapIds_comp (binding : TypedLocalBinding)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    (binding.mapIds first).mapIds second = binding.mapIds (second ∘ first) := rfl

private theorem nodup_map_injective {α β : Type} (mapping : α → β)
    (injective : Function.Injective mapping) {values : List α} (distinct : values.Nodup) :
    (values.map mapping).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
        exact absent (injective same ▸ originalMember)
      · exact ih tailDistinct

namespace LocalInputs

def mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) : LocalInputs where
  bindings := inputs.bindings.map (TypedLocalBinding.mapIds mapping)
  ids_nodup := by
    simpa [TypedLocalBinding.mapIds, List.map_map, Function.comp_def] using
      nodup_map_injective mapping injective inputs.ids_nodup

@[simp] theorem mapIds_bindings (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).bindings =
      inputs.bindings.map (TypedLocalBinding.mapIds mapping) := rfl

@[simp] theorem mapIds_ids (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).ids = inputs.ids.map mapping := by
  simp [ids, mapIds, TypedLocalBinding.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_names (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).names = LocalNameTable.mapIds mapping inputs.names := by
  simp [names, mapIds, TypedLocalBinding.mapIds, LocalNameTable.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_context (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).context = Resolved.LocalScope.mapIds mapping inputs.context := by
  simp [context, mapIds, TypedLocalBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_environment (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).environment = Resolved.LocalScope.mapIds mapping inputs.environment := by
  simp [environment, mapIds, TypedLocalBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_id (inputs : LocalInputs) :
    inputs.mapIds id (fun _ _ same => same) = inputs := by
  cases inputs
  simp [mapIds, show TypedLocalBinding.mapIds id = id from funext TypedLocalBinding.mapIds_id]

theorem mapIds_comp (inputs : LocalInputs) (first second : Resolved.LocalId → Resolved.LocalId)
    (firstInjective : Function.Injective first) (secondInjective : Function.Injective second) :
    (inputs.mapIds first firstInjective).mapIds second secondInjective =
      inputs.mapIds (second ∘ first) (secondInjective.comp firstInjective) := by
  cases inputs
  simp [mapIds, List.map_map, Function.comp_def, TypedLocalBinding.mapIds_comp]

end LocalInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsRenamingProperties`
-/

/-! Identity relabeling leaves checked Core and runtime value lists unchanged.
The runner agrees at identical fuel, including its entire suspended state. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem check?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (source : Syntax.Expr) :
    (inputs.mapIds mapping injective).check? source = inputs.check? source := by
  simp only [check?, mapIds_names, mapIds_context, elaborateLocalExpression?_mapIds mapping injective]

/-- No successful checking or sufficient fuel premise: both absent and all
present results, including exact out-of-fuel states, are unchanged. -/
theorem run?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    (inputs.mapIds mapping injective).run? fuel source store = inputs.run? fuel source store := by
  simp only [run?, check?_mapIds, mapIds_environment, Resolved.LocalScope.values_mapIds]

theorem hasType_mapIds_iff (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType (inputs.mapIds mapping injective).names
        (inputs.mapIds mapping injective).context source type ↔
      LocalExpressionHasType inputs.names inputs.context source type := by
  simp only [mapIds_names, mapIds_context, localExpressionHasType_mapIds_iff mapping injective]

theorem evaluates_mapIds_iff (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {source : Syntax.Expr} {value : Core.Value}
    {initialStore finalStore : Core.Store} :
    LocalExpressionEvaluates (inputs.mapIds mapping injective).names
        (inputs.mapIds mapping injective).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore := by
  simp only [mapIds_names, mapIds_environment, localExpressionEvaluates_mapIds_iff mapping injective]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsTypeErasure`
-/

/-! Erase supplied values and their typing evidence while retaining the exact
ordered static rows. This direction requires no runtime-value reconstruction. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def toTypeInputs (inputs : LocalInputs) : LocalTypeInputs where
  bindings := inputs.bindings.map fun binding =>
    { name := binding.name, id := binding.id, type := binding.type }
  ids_nodup := by
    simpa only [List.map_map, Function.comp_def] using inputs.ids_nodup

@[simp] theorem toTypeInputs_ids (inputs : LocalInputs) :
    inputs.toTypeInputs.ids = inputs.ids := by
  simp only [toTypeInputs, LocalTypeInputs.ids, ids, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_names (inputs : LocalInputs) :
    inputs.toTypeInputs.names = inputs.names := by
  simp only [toTypeInputs, LocalTypeInputs.names, names, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_context (inputs : LocalInputs) :
    inputs.toTypeInputs.context = inputs.context := by
  simp only [toTypeInputs, LocalTypeInputs.context, context, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_empty : empty.toTypeInputs = LocalTypeInputs.empty := rfl

@[simp] theorem toTypeInputs_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).toTypeInputs =
      inputs.toTypeInputs.bindFresh owner name type := by
  cases inputs
  simp only [toTypeInputs, bindFresh, LocalTypeInputs.bindFresh, LocalTypeInputs.ids, ids,
    List.map_cons, List.map_map, Function.comp_def]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsTypeErasureRenamingProperties`
-/

/-! Relabeling already supplied inputs commutes with erasing their values.
This constructs no inhabitants for arbitrary type-only inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

@[simp] theorem toTypeInputs_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).toTypeInputs =
      inputs.toTypeInputs.mapIds mapping injective := by
  cases inputs
  simp only [toTypeInputs, mapIds, LocalTypeInputs.mapIds, List.map_map,
    Function.comp_def, TypedLocalBinding.mapIds, LocalTypeBinding.mapIds]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCost`
-/

/-! Independent successful source evaluation indexed by Core transition count.
Costs do not measure frontend traversal, lookup, decoding, gas, or elapsed time.
Unselected branches carry no premise; strict Word operands and tuple elements retain their order
and both store endpoints. This relation does not assume execution or erasure. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | identifier {store : Core.Store} {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalExpressionEvaluatesWithCost table environment store
        { span, value := .identifier name } value store 1
  | wordLiteral {store : Core.Store} {span : Syntax.SourceSpan}
      {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      LocalExpressionEvaluatesWithCost table environment store
        { span, value := .literal literal } (.word word) store 1
  | group {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan}
      {inner : Syntax.Expr} {value : Core.Value} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore inner value finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .group inner } value finalStore childCost
  | unit {store : Core.Store} {span tupleSpan : Syntax.SourceSpan} :
      LocalExpressionEvaluatesWithCost table environment store
        { span, value := .tuple ⟨tupleSpan, []⟩ } .unit store 1
  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left leftValue middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right rightValue finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .tuple ⟨tupleSpan, [left, right]⟩ }
        (.pair leftValue rightValue) finalStore (leftCost + rightCost + 3)
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value} {headCost tailCost : Nat}
      (headEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore first headValue middleStore headCost)
      (tailEvaluation : LocalExpressionEvaluatesWithCost table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore tailCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headValue tailValue) finalStore (headCost + tailCost + 3)
  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore operand (.bool value) finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
        (.bool (!value)) finalStore (childCost + 2)
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word} {childCost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment
        initialStore operand (.word value) finalStore childCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand }
        (.word value.bitNot) finalStore (childCost + 2)
  | add {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .add⟩ right }
        (.word (leftValue.add rightValue)) finalStore (leftCost + rightCost + 3)
  | subtract {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
        (.word (leftValue.sub rightValue)) finalStore (leftCost + rightCost + 3)
  | multiply {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
        (.word (leftValue.mul rightValue)) finalStore (leftCost + rightCost + 3)
  | divide {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
        (.word (leftValue.udiv rightValue)) finalStore (leftCost + rightCost + 3)
  | modulo {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
        (.word (leftValue.umod rightValue)) finalStore (leftCost + rightCost + 3)
  | bitAnd {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
        (.word (leftValue.bitAnd rightValue)) finalStore (leftCost + rightCost + 3)
  | bitOr {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
        (.word (leftValue.bitOr rightValue)) finalStore (leftCost + rightCost + 3)
  | bitXor {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
        (.word (leftValue.bitXor rightValue)) finalStore (leftCost + rightCost + 3)
  | greater {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
        (.bool (decide (leftValue > rightValue))) finalStore (leftCost + rightCost + 3)
  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .less⟩ right }
        (.bool (decide (leftValue < rightValue))) finalStore (leftCost + rightCost + 9)
  | equal {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
        (.bool (leftValue == rightValue)) finalStore (leftCost + rightCost + 3)
  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
        (.bool (!(leftValue == rightValue))) finalStore (leftCost + rightCost + 5)
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
        (.bool (!(decide (leftValue > rightValue)))) finalStore (leftCost + rightCost + 5)
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
        (.bool (!(decide (leftValue < rightValue)))) finalStore (leftCost + rightCost + 11)
  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool true) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
        value finalStore (leftCost + rightCost + 2)
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {leftCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool false) finalStore leftCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
        (.bool false) finalStore (leftCost + 3)
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {leftCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool true) finalStore leftCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
        (.bool true) finalStore (leftCost + 3)
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore left (.bool false) middleStore leftCost)
      (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
        value finalStore (leftCost + rightCost + 2)
  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment initialStore
        condition (.bool true) middleStore conditionCost)
      (branchEvaluation : LocalExpressionEvaluatesWithCost table environment middleStore
        thenBranch value finalStore branchCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch }
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment initialStore
        condition (.bool false) middleStore conditionCost)
      (branchEvaluation : LocalExpressionEvaluatesWithCost table environment middleStore
        elseBranch value finalStore branchCost) :
      LocalExpressionEvaluatesWithCost table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch }
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationEvaluation`
-/

/-! Successful evaluation of an original root call. The actual closure body
and captures are supplied by evaluation of the original callee, not by static
typing or a checker. Its body may change the store or fail to terminate. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalFunctionApplicationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | call {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      (functionEvaluation : LocalExpressionEvaluates table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore)
      (argumentEvaluation : LocalExpressionEvaluates table environment argumentStore
        argument argumentValue bodyStore)
      (bodyEvaluation : Core.Evaluates (argumentValue :: captured) bodyStore body result finalStore) :
      LocalFunctionApplicationEvaluates table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

/-- Cost is the two pure child costs plus the exact actual-body path and three
application transitions. No source-only bound or unchanged-store law is assumed. -/
inductive LocalFunctionApplicationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | call {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      {functionCost argumentCost bodyCost : Nat}
      (functionEvaluation : LocalExpressionEvaluatesWithCost table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore functionCost)
      (argumentEvaluation : LocalExpressionEvaluatesWithCost table environment argumentStore
        argument argumentValue bodyStore argumentCost)
      (bodyPath : Core.Steps bodyCost
        (Core.State.initial body (argumentValue :: captured) bodyStore)
        (Core.State.final result finalStore)) :
      LocalFunctionApplicationEvaluatesWithCost table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore
        (functionCost + argumentCost + bodyCost + 3)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostErasureProperties`
-/

/-! Raw source evaluation and independent transition costs have the same
successful outcomes. Erasure and cost existence need no Core translation,
including evaluations with skipped unresolved or unsupported syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.erase {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
  induction evaluation with
  | identifier named found => exact .identifier named found
  | wordLiteral meaning => exact .wordLiteral meaning
  | unit => exact .unit
  | group _ ih => exact .group ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
  | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
  | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
  | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
  | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
  | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
  | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
  | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
  | less _ _ leftIH rightIH => exact .less leftIH rightIH
  | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
  | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
  | andFalse _ ih => exact .andFalse ih
  | orTrue _ ih => exact .orTrue ih
  | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
  | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

theorem LocalExpressionEvaluates.exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    ∃ cost, LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  induction evaluation with
  | identifier named found => exact ⟨1, .identifier named found⟩
  | wordLiteral meaning => exact ⟨1, .wordLiteral meaning⟩
  | unit => exact ⟨1, .unit⟩
  | group _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .group child⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .pair left right⟩
  | many _ _ headIH tailIH =>
      obtain ⟨headCost, head⟩ := headIH
      obtain ⟨tailCost, tail⟩ := tailIH
      exact ⟨_, .many head tail⟩
  | logicalNot _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .logicalNot child⟩
  | bitNot _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .bitNot child⟩
  | add _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .add left right⟩
  | subtract _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .subtract left right⟩
  | multiply _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .multiply left right⟩
  | divide _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .divide left right⟩
  | modulo _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .modulo left right⟩
  | bitAnd _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitAnd left right⟩
  | bitOr _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitOr left right⟩
  | bitXor _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .bitXor left right⟩
  | greater _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .greater left right⟩
  | less _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .less left right⟩
  | equal _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .equal left right⟩
  | notEqual _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .notEqual left right⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .lessEqual left right⟩
  | greaterEqual _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .greaterEqual left right⟩
  | andTrue _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .andTrue left right⟩
  | andFalse _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .andFalse child⟩
  | orTrue _ ih =>
      obtain ⟨cost, child⟩ := ih
      exact ⟨_, .orTrue child⟩
  | orFalse _ _ leftIH rightIH =>
      obtain ⟨leftCost, left⟩ := leftIH
      obtain ⟨rightCost, right⟩ := rightIH
      exact ⟨_, .orFalse left right⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨conditionCost, condition⟩ := conditionIH
      obtain ⟨branchCost, branch⟩ := branchIH
      exact ⟨_, .ifTrue condition branch⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨conditionCost, condition⟩ := conditionIH
      obtain ⟨branchCost, branch⟩ := branchIH
      exact ⟨_, .ifFalse condition branch⟩

theorem localExpressionEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalExpressionEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨LocalExpressionEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalExpressionEvaluatesWithCost.store_eq {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) : finalStore = initialStore :=
  evaluation.erase.store_eq

theorem LocalExpressionEvaluatesWithCost.cost_pos {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost) : 0 < cost := by
  induction evaluation <;> omega

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostProperties`
-/

/-! Joint uniqueness of independent source values, stores and transition costs.
The historical import path also retains erasure and cost-existence interfaces. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Value, final store, and cost are jointly determined without whole source
resolution or typing. Incompatible branch choices contradict child uniqueness. -/
theorem LocalExpressionEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction leftEvaluation generalizing right rightStore rightCost with
  | identifier named found =>
      cases rightEvaluation with
      | identifier otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl, rfl⟩
  | wordLiteral meaning =>
      cases rightEvaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl, rfl⟩
  | unit => cases rightEvaluation; exact ⟨rfl, rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | many _ _ headIH tailIH =>
      cases rightEvaluation with
      | many headChild tailChild =>
          obtain ⟨sameHead, rfl, rfl⟩ := headIH headChild
          obtain ⟨sameTail, storeEq, rfl⟩ := tailIH tailChild
          cases sameHead; cases sameTail
          exact ⟨rfl, storeEq, rfl⟩
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq, rfl⟩ := ih child
          cases same
          exact ⟨rfl, storeEq, rfl⟩
  | bitNot _ ih =>
      cases rightEvaluation with
      | bitNot child =>
          obtain ⟨same, storeEq, rfl⟩ := ih child
          cases same
          exact ⟨rfl, storeEq, rfl⟩
  | add _ _ leftIH rightIH =>
      cases rightEvaluation with
      | add leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | subtract _ _ leftIH rightIH =>
      cases rightEvaluation with
      | subtract leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | multiply _ _ leftIH rightIH =>
      cases rightEvaluation with
      | multiply leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | divide _ _ leftIH rightIH =>
      cases rightEvaluation with
      | divide leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | modulo _ _ leftIH rightIH =>
      cases rightEvaluation with
      | modulo leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | bitAnd _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitAnd leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | bitOr _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitOr leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | bitXor _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitXor leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | greater _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greater leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | less _ _ leftIH rightIH =>
      cases rightEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | equal _ _ leftIH rightIH =>
      cases rightEvaluation with
      | equal leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | notEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | lessEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | greaterEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greaterEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq, rfl⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases rightEvaluation with
      | andTrue leftChild rightChild =>
          obtain ⟨_, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨same, storeEq, rfl⟩ := rightIH rightChild
          exact ⟨same, storeEq, rfl⟩
      | andFalse leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | andFalse _ leftIH =>
      cases rightEvaluation with
      | andFalse leftChild =>
          obtain ⟨_, storeEq, rfl⟩ := leftIH leftChild
          exact ⟨rfl, storeEq, rfl⟩
      | andTrue leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orTrue _ leftIH =>
      cases rightEvaluation with
      | orTrue leftChild =>
          obtain ⟨_, storeEq, rfl⟩ := leftIH leftChild
          exact ⟨rfl, storeEq, rfl⟩
      | orFalse leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orFalse _ _ leftIH rightIH =>
      cases rightEvaluation with
      | orFalse leftChild rightChild =>
          obtain ⟨_, rfl, rfl⟩ := leftIH leftChild
          obtain ⟨same, storeEq, rfl⟩ := rightIH rightChild
          exact ⟨same, storeEq, rfl⟩
      | orTrue leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨same, storeEq, rfl⟩ := branchIH branch
          exact ⟨same, storeEq, rfl⟩
      | ifFalse condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifFalse condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨same, storeEq, rfl⟩ := branchIH branch
          exact ⟨same, storeEq, rfl⟩
      | ifTrue condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible

theorem LocalExpressionEvaluatesWithCost.cost_unique {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) : leftCost = rightCost :=
  (leftEvaluation.deterministic rightEvaluation).2.2

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationEvaluationProperties`
-/

/-! Successful source-call evaluation and exact costs retain the actual closure
and its store-threaded body. These laws need neither checking nor typed inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalFunctionApplicationEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalFunctionApplicationEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases leftEvaluation with
  | call functionEvaluation argumentEvaluation bodyEvaluation =>
      cases rightEvaluation with
      | call otherFunction otherArgument otherBody =>
          obtain ⟨sameFunction, rfl⟩ := functionEvaluation.deterministic otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl⟩ := argumentEvaluation.deterministic otherArgument
          exact Core.evaluation_deterministic bodyEvaluation otherBody

theorem LocalFunctionApplicationEvaluatesWithCost.erase {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore := by
  cases evaluation with
  | call functionEvaluation argumentEvaluation bodyPath =>
      exact .call functionEvaluation.erase argumentEvaluation.erase
        (Core.steps_from_initial_sound bodyPath)

theorem LocalFunctionApplicationEvaluates.exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
    ∃ cost, LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  cases evaluation with
  | call functionEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨_, functionCosted⟩ := functionEvaluation.exists_cost
      obtain ⟨_, argumentCosted⟩ := argumentEvaluation.exists_cost
      obtain ⟨_, bodyPath⟩ := bodyEvaluation.toSteps
      exact ⟨_, .call functionCosted argumentCosted bodyPath⟩

theorem localFunctionApplicationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalFunctionApplicationEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨LocalFunctionApplicationEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem LocalFunctionApplicationEvaluatesWithCost.cost_pos {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost) : 0 < cost := by
  cases evaluation
  omega

/-- Child determinism fixes the actual closure and argument before comparing
the two closed paths for its body; no equality of static function tags is used. -/
theorem LocalFunctionApplicationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | call functionEvaluation argumentEvaluation bodyPath =>
      cases rightEvaluation with
      | call otherFunction otherArgument otherPath =>
          obtain ⟨sameFunction, rfl, rfl⟩ := functionEvaluation.deterministic otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl, rfl⟩ := argumentEvaluation.deterministic otherArgument
          obtain ⟨rfl, sameValue, sameStore⟩ := bodyPath.final_unique otherPath
          exact ⟨sameValue, sameStore, rfl⟩

theorem LocalFunctionApplicationEvaluatesWithCost.cost_unique {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) : leftCost = rightCost :=
  (leftEvaluation.deterministic rightEvaluation).2.2

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostRenamingProperties`
-/

/-! Injective identity relabeling preserves independent source costs. Only
identifier leaves use erased evaluation to recover the existing lookup laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Simultaneous injective ID relabeling preserves raw value, both stores, and
cost. Whole resolution and typing are not required, even for skipped syntax. -/
theorem localExpressionEvaluatesWithCost_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore cost ↔
      LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mp
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier oldNamed oldFound => exact .identifier oldNamed oldFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | unit => exact .unit
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mpr
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier newNamed newFound => exact .identifier newNamed newFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | unit => exact .unit
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostInvariance`
-/

/-! Structural preservation of independent source costs under identity
relabeling and unused-name insertion. Erased evaluation is used only at
identifier leaves to recover existing lookup laws, not to equate costs. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Avoidance covers every written child, including unselected branches and
arbitrary literal payloads. Freshness alone does not prevent spelling shadowing.
This is an exact raw-cost law, not equality of suspended machine states. -/
theorem AvoidsLocalName.bindFresh_cost_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {result : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).environment
        initialStore source result finalStore cost ↔
      LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        initialStore source result finalStore cost := by
  induction avoids generalizing initialStore finalStore result cost with
  | identifier different =>
      constructor
      · intro evaluation
        have ordinary := ((AvoidsLocalName.identifier different).bindFresh_evaluates_iff
          inputs owner newType newValue valueTyped).mp evaluation.erase
        cases evaluation with
        | identifier _ _ =>
            cases ordinary with
            | identifier named found => exact .identifier named found
      · intro evaluation
        have ordinary := ((AvoidsLocalName.identifier different).bindFresh_evaluates_iff
          inputs owner newType newValue valueTyped).mpr evaluation.erase
        cases evaluation with
        | identifier _ _ =>
            cases ordinary with
            | identifier named found => exact .identifier named found
  | literal =>
      constructor
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
  | unit => constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | many _ _ headIH tailIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | many head tail => exact .many (headIH.mp head) (tailIH.mp tail)
      · intro evaluation
        cases evaluation with
        | many head tail => exact .many (headIH.mpr head) (tailIH.mpr tail)
  | logicalNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mp left) (rightIH.mp right)
        | andFalse left => exact .andFalse (leftIH.mp left)
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mpr left) (rightIH.mpr right)
        | andFalse left => exact .andFalse (leftIH.mpr left)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mp left)
        | orFalse left right => exact .orFalse (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mpr left)
        | orFalse left right => exact .orFalse (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mp condition) (thenIH.mp branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mp condition) (elseIH.mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mpr condition) (thenIH.mpr branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mpr condition) (elseIH.mpr branch)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostStepComposition`
-/

/-! Exact continuation-local paths for the primitive forms used by the
canonical cost bridge. These lemmas count transitions without executing a runner. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem unary {environment : Environment} {initialStore finalStore : Store}
    {op : UnaryOp} {operand : Expr} {operandValue result : Value}
    {continuation : List Frame} {childCost : Nat}
    (child : Steps childCost
      ⟨.eval operand environment, .unaryApply op :: continuation, initialStore⟩
      ⟨.ret operandValue, .unaryApply op :: continuation, finalStore⟩)
    (applied : op.apply operandValue = some result) :
    Steps (childCost + 2)
      ⟨.eval (.unary op operand) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterUnary (child.trans (.cons (.applyUnary applied) .refl))
  simpa only [Nat.add_assoc] using path

theorem binary {environment : Environment} {initialStore middleStore finalStore : Store}
    {op : BinaryOp} {left right : Expr} {leftValue rightValue result : Value}
    {continuation : List Frame} {leftCost rightCost : Nat}
    (leftPath : Steps leftCost
      ⟨.eval left environment, .binaryRight op right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .binaryRight op right environment :: continuation, middleStore⟩)
    (rightPath : Steps rightCost
      ⟨.eval right environment, .binaryApply op leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .binaryApply op leftValue :: continuation, finalStore⟩)
    (applied : op.apply leftValue rightValue = some result) :
    Steps (leftCost + rightCost + 3)
      ⟨.eval (.binary op left right) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterBinary
    (leftPath.trans (.cons .enterBinaryRight (rightPath.trans (.cons (.applyBinary applied) .refl))))
  simpa only [Nat.add_assoc] using path

theorem ifTrue {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool true), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval thenBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseTrue branchPath))
  simpa only [Nat.add_assoc] using path

theorem ifFalse {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool false), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval elseBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseFalse branchPath))
  simpa only [Nat.add_assoc] using path

end Solcore.Frontend.CostStepComposition

/-!
## Consolidated module: `Solcore.Frontend.WordLessCostStepComposition`
-/

/-! Exact ordered paths for existing Core lets and the derived less-than tree.
The weakened right path is an explicit premise, not a general weakening claim. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem letE {environment : Environment} {initialStore middleStore finalStore : Store}
    {value body : Expr} {boundValue result : Value} {continuation : List Frame}
    {valueCost bodyCost : Nat}
    (valuePath : Steps valueCost
      ⟨.eval value environment, .letBody body environment :: continuation, initialStore⟩
      ⟨.ret boundValue, .letBody body environment :: continuation, middleStore⟩)
    (bodyPath : Steps bodyCost
      ⟨.eval body (boundValue :: environment), continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (valueCost + bodyCost + 2)
      ⟨.eval (.letE value body) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterLet (valuePath.trans (.cons .bindLet bodyPath))
  simpa only [Nat.add_assoc] using path

/-- The original left expression runs first. The supplied right path explicitly
uses its weakened Core under the retained left value. The generated comparison
then reads right at zero and left at one without re-evaluating either operand. -/
theorem wordLt {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word} {leftCost rightCost : Nat}
    (leftPath : ∀ continuation, Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost
      ⟨.eval (right.weakenAt 0) (.word leftWord :: environment), continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (continuation : List Frame) :
    Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ := by
  have compared : Steps 5
      ⟨.eval (.binary .wordGt (.var 0) (.var 1))
        (.word rightWord :: .word leftWord :: environment), continuation, finalStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ :=
    binary (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl
  have inner := letE (rightPath _) compared
  have outer := letE (leftPath _) inner
  simpa only [Expr.wordLt_expansion, Nat.add_assoc] using outer

end Solcore.Frontend.CostStepComposition

/-!
## Consolidated module: `Solcore.Frontend.WordLessLocalRightCostProperties`
-/

/-! Ordered comparison costs from the two original operand paths. Exact
insertion discharges the weakened-right premise without restricting left
effects, adding runtime typing assumptions, or changing the outer continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

theorem wordLt_of_local_right
    {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word} {leftCost rightCost : Nat}
    (leftPath : ∀ continuation, Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost
      ⟨.eval right environment, continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (rightFragment : right.LocalFragment) (continuation : List Frame) :
    Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ :=
  wordLt leftPath
    (fun outer => (rightPath []).weakenAt_zero_localFragment rightFragment (.word leftWord) outer)
    continuation

end Solcore.Frontend.CostStepComposition

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostCorrespondence`
-/

/-! Independent source costs are exact Core path lengths. Whole structural
resolution and runtime identity-order lowering are explicit; no typing or
runtime store assumptions are needed once a cost derivation is supplied. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem pair_steps
    {environment : Core.Environment} {initialStore middleStore finalStore : Core.Store}
    {left right : Core.Expr} {leftValue rightValue : Core.Value}
    {continuation : List Core.Frame} {leftCost rightCost : Nat}
    (leftPath : Core.Steps leftCost
      ⟨.eval left environment, .pairRight right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .pairRight right environment :: continuation, middleStore⟩)
    (rightPath : Core.Steps rightCost
      ⟨.eval right environment, .pairApply leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .pairApply leftValue :: continuation, finalStore⟩) :
    Core.Steps (leftCost + rightCost + 3)
      ⟨.eval (.pair left right) environment, continuation, initialStore⟩
      ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ := by
  have path := Core.Steps.cons .enterPair
    (leftPath.trans (.cons .enterPairRight (rightPath.trans (.cons .applyPair .refl))))
  simpa only [Nat.add_assoc] using path

theorem LocalExpressionEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction evaluation generalizing resolved core continuation with
  | identifier named found =>
      cases resolution with
      | identifier otherNamed =>
          cases named.id_unique otherNamed
          cases lowered with
          | var indexed =>
              exact .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)) .refl
  | wordLiteral meaning =>
      cases resolution with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          cases lowered
          exact .cons .word .refl
  | unit => cases resolution; cases lowered; exact .cons .unit .refl
  | group _ ih =>
      cases resolution with
      | group child => exact ih child lowered continuation
  | pair _ _ leftIH rightIH =>
      cases resolution with
      | pair leftChild rightChild =>
          cases lowered with
          | pair lowerLeft lowerRight =>
              exact pair_steps (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _)
  | many _ _ headIH tailIH =>
      cases resolution with
      | many headChild tailChild =>
          cases lowered with
          | pair lowerHead lowerTail =>
              exact pair_steps (headIH headChild lowerHead _) (tailIH tailChild lowerTail _)
  | logicalNot _ ih =>
      cases resolution with
      | logicalNot child =>
          cases lowered with
          | unary lowerChild => exact CostStepComposition.unary (ih child lowerChild _) rfl
  | bitNot _ ih =>
      cases resolution with
      | bitNot child =>
          cases lowered with
          | unary lowerChild => exact CostStepComposition.unary (ih child lowerChild _) rfl
  | add _ _ leftIH rightIH =>
      cases resolution with
      | add leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | subtract _ _ leftIH rightIH =>
      cases resolution with
      | subtract leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | multiply _ _ leftIH rightIH =>
      cases resolution with
      | multiply leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | divide _ _ leftIH rightIH =>
      cases resolution with
      | divide leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | modulo _ _ leftIH rightIH =>
      cases resolution with
      | modulo leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitAnd _ _ leftIH rightIH =>
      cases resolution with
      | bitAnd leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitOr _ _ leftIH rightIH =>
      cases resolution with
      | bitOr leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitXor _ _ leftIH rightIH =>
      cases resolution with
      | bitXor leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | greater _ _ leftIH rightIH =>
      cases resolution with
      | greater leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | less _ _ leftIH rightIH =>
      cases resolution with
      | less leftChild rightChild =>
          cases lowered with
          | wordLt lowerLeft lowerRight =>
              exact CostStepComposition.wordLt_of_local_right
                (leftIH leftChild lowerLeft) (rightIH rightChild lowerRight)
                lowerRight.localFragment continuation
  | equal _ _ leftIH rightIH =>
      cases resolution with
      | equal leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | notEqual _ _ leftIH rightIH =>
      cases resolution with
      | notEqual leftChild rightChild =>
          cases lowered with
          | unary lowerEquality =>
              cases lowerEquality with
              | binary lowerLeft lowerRight =>
                  simpa only [Nat.add_assoc] using CostStepComposition.unary
                    (CostStepComposition.binary
                      (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases resolution with
      | lessEqual leftChild rightChild =>
          cases lowered with
          | unary lowerComparison =>
              cases lowerComparison with
              | binary lowerLeft lowerRight =>
                  simpa only [Nat.add_assoc] using CostStepComposition.unary
                    (CostStepComposition.binary
                      (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl) rfl
  | greaterEqual _ _ leftIH rightIH =>
      cases resolution with
      | greaterEqual leftChild rightChild =>
          cases lowered with
          | unary lowerComparison =>
              cases lowerComparison with
              | wordLt lowerLeft lowerRight =>
                  simpa only [Nat.add_assoc] using CostStepComposition.unary
                    (CostStepComposition.wordLt_of_local_right
                      (leftIH leftChild lowerLeft) (rightIH rightChild lowerRight)
                      lowerRight.localFragment (.unaryApply .boolNot :: continuation)) rfl
  | andTrue _ _ leftIH rightIH =>
      cases resolution with
      | logicalAnd leftChild rightChild =>
          cases lowered with
          | ifE lowerLeft lowerRight _ =>
              exact CostStepComposition.ifTrue
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _)
  | andFalse _ leftIH =>
      cases resolution with
      | logicalAnd leftChild _ =>
          cases lowered with
          | ifE lowerLeft _ lowerConstant =>
              cases lowerConstant
              simpa only [Nat.add_assoc] using CostStepComposition.ifFalse
                (leftIH leftChild lowerLeft _) (.cons .bool .refl)
  | orTrue _ leftIH =>
      cases resolution with
      | logicalOr leftChild _ =>
          cases lowered with
          | ifE lowerLeft lowerConstant _ =>
              cases lowerConstant
              simpa only [Nat.add_assoc] using CostStepComposition.ifTrue
                (leftIH leftChild lowerLeft _) (.cons .bool .refl)
  | orFalse _ _ leftIH rightIH =>
      cases resolution with
      | logicalOr leftChild rightChild =>
          cases lowered with
          | ifE lowerLeft _ lowerRight =>
              exact CostStepComposition.ifFalse
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _)
  | ifTrue _ _ conditionIH branchIH =>
      cases resolution with
      | conditional conditionChild branchChild _ =>
          cases lowered with
          | ifE lowerCondition lowerBranch _ =>
              exact CostStepComposition.ifTrue
                (conditionIH conditionChild lowerCondition _) (branchIH branchChild lowerBranch _)
  | ifFalse _ _ conditionIH branchIH =>
      cases resolution with
      | conditional conditionChild _ branchChild =>
          cases lowered with
          | ifE lowerCondition _ lowerBranch =>
              exact CostStepComposition.ifFalse
                (conditionIH conditionChild lowerCondition _) (branchIH branchChild lowerBranch _)

theorem LocalExpressionEvaluatesWithCost.toSteps
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    Core.Steps cost
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.toStepsWithContinuation resolution lowered []

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationExecutionProperties`
-/

/-! Exact static provenance connects independent calls to the original Core
application. Ordered runtime IDs suffice; actual closure tags, captures, body
costs and final stores are not inferred from static context types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  cases elaboration with
  | call functionResolution functionLowered _ argumentResolution argumentLowered _ =>
      rw [← sameIds] at functionLowered argumentLowered
      constructor
      · intro evaluation
        cases evaluation with
        | call functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((functionResolution.core_evaluates_iff functionLowered).mp functionEvaluation)
              ((argumentResolution.core_evaluates_iff argumentLowered).mp argumentEvaluation)
              bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .call ((functionResolution.core_evaluates_iff functionLowered).mpr functionEvaluation)
              ((argumentResolution.core_evaluates_iff argumentLowered).mpr argumentEvaluation)
              bodyEvaluation

/-- One supplied cost works for every continuation, including pending frames
that may fail after this endpoint. The actual body path remains unchanged. -/
theorem LocalFunctionApplicationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | call functionResolution functionLowered _ argumentResolution argumentLowered _ =>
      rw [← sameIds] at functionLowered argumentLowered
      cases evaluation with
      | call functionEvaluation argumentEvaluation bodyPath =>
          exact CostStepComposition.apply
            (functionEvaluation.toStepsWithContinuation functionResolution functionLowered _)
            (argumentEvaluation.toStepsWithContinuation argumentResolution argumentLowered _) bodyPath

theorem LocalFunctionApplicationEvaluatesWithCost.toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.toStepsWithContinuation elaboration sameIds []

theorem LocalFunctionApplicationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toSteps elaboration sameIds
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := evaluation.exists_cost
    have sameCost := (path.final_unique (actual.toSteps elaboration sameIds)).1
    exact sameCost.symm ▸ actual

/-- Cost is chosen before all continuations. Reflection uses the empty one,
whose return endpoint really is final; arbitrary endpoints need not be final. -/
theorem LocalFunctionApplicationElaborates.evaluates_iff_exists_uniform_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, ∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  constructor
  · intro evaluation
    obtain ⟨cost, exactEvaluation⟩ := evaluation.exists_cost
    exact ⟨cost, exactEvaluation.toStepsWithContinuation elaboration sameIds⟩
  · rintro ⟨_, paths⟩
    exact (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound (paths []))

theorem elaborateLocalFunctionApplication?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  (elaborateLocalFunctionApplication?_sound accepted).evaluates_iff sameIds

theorem elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalFunctionApplicationEvaluatesWithCost table environment
      initialStore source value finalStore cost ↔
      Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
        (Core.State.final value finalStore) :=
  (elaborateLocalFunctionApplication?_sound accepted).evaluatesWithCost_iff_steps sameIds

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalFunctionApplicationRuntimeSafetyProperties`
-/

/-! Runtime-world safety for the actual original call. Captures and referenced
locations share the supplied typed store. Structural value typing alone cannot
discharge these premises, and actual successful costs are not source bounds. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationEvaluates.preserves_runtime_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world initialStore) :
    ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
      Core.RuntimeValueHasType finalWorld value type :=
  Core.evaluation_preserves_type ((elaboration.evaluates_iff sameIds).mp evaluation)
    elaboration.core_hasType environmentTyped storeTyped

/-- Whole source typing supplies successful evaluation only together with the
actual aligned environment and store typed in the same runtime world. -/
theorem LocalFunctionApplicationHasType.runtime_evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost table environment store source value finalStore cost := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have definitionsWellFormed : Core.DataEnvironment.WellFormed [] := by
    intro definition member
    cases member
  obtain ⟨finalWorld, finalStore, value, extension, finalTyped, evaluated, valueTyped⟩ :=
    Core.well_typed_evaluates elaboration.core_hasType definitionsWellFormed environmentTyped storeTyped
  obtain ⟨cost, exactEvaluation⟩ := ((elaboration.evaluates_iff sameIds).mpr evaluated).exists_cost
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, exactEvaluation⟩

/-- One actual successful cost gives all continuation-local paths and both
closed fuel thresholds. No completion claim is made for untyped pending frames. -/
theorem LocalFunctionApplicationElaborates.runtime_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost table environment store source value finalStore cost ∧
      (∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core (Resolved.LocalScope.values environment), continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      ∀ fuel, (Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values environment) store) =
            .outOfFuel checkpoint) ↔ fuel < cost) := by
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation⟩ :=
    elaboration.hasType.runtime_evaluates sameIds environmentTyped storeTyped
  have path := evaluation.toSteps elaboration sameIds
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation,
    evaluation.toStepsWithContinuation elaboration sameIds,
    fun _ => ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩⟩

theorem elaborateLocalFunctionApplication?_runtime_run_done_sound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {world : Core.StoreTyping} {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (storeTyped : Core.StoreHasTypes world initialStore)
    (completed : Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
        .done value finalStore) :
    LocalFunctionApplicationEvaluates table environment initialStore source value finalStore ∧
      ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
        Core.RuntimeValueHasType finalWorld value type := by
  have elaboration := elaborateLocalFunctionApplication?_sound accepted
  have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.runStateful_evaluation_sound completed)
  exact ⟨evaluation, evaluation.preserves_runtime_type elaboration sameIds environmentTyped storeTyped⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsApplicationProperties`
-/

/-! The separate endpoint preserves its exact checked Core and every machine
result. Completion corresponds to whole typing plus independent source
evaluation; structural input typing alone adds no runtime value or store claim. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkApplication?_iff_elaborates {inputs : LocalInputs} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    inputs.checkApplication? source = some (core, type) ↔
      LocalFunctionApplicationElaborates inputs.names inputs.context source core type :=
  elaborateLocalFunctionApplication?_iff

theorem checkApplication?_iff_hasType {inputs : LocalInputs} {source : Syntax.Expr}
    {type : Core.Ty} :
    (∃ core, inputs.checkApplication? source = some (core, type)) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type := by
  constructor
  · rintro ⟨core, accepted⟩
    exact (checkApplication?_iff_elaborates.mp accepted).hasType
  · intro typing
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    exact ⟨core, checkApplication?_iff_elaborates.mpr elaboration⟩

theorem runApplication?_eq_some_iff {inputs : LocalInputs} {source : Syntax.Expr}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runApplication? fuel source store = some (type, result) ↔
      ∃ core, inputs.checkApplication? source = some (core, type) ∧
        Core.runStateful fuel
          (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runApplication?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

/-- Only the static gate can produce outer absence, at every fuel and store. -/
theorem runApplication?_eq_none_iff {inputs : LocalInputs} {source : Syntax.Expr}
    (fuel : Nat) (store : Core.Store) :
    inputs.runApplication? fuel source store = none ↔ inputs.checkApplication? source = none := by
  cases checked : inputs.checkApplication? source with
  | none => simp [runApplication?, checked]
  | some pair => cases pair; simp [runApplication?, checked]

/-- An observed completion reflects source evaluation, not runtime typing of
the value or equality of the initial and final stores. -/
theorem runApplication?_done_sound {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value}
    (result : inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) :
    LocalFunctionApplicationEvaluates inputs.names inputs.environment
      initialStore source value finalStore := by
  obtain ⟨core, checked, execution⟩ := runApplication?_eq_some_iff.mp result
  exact ((checkApplication?_iff_elaborates.mp checked).evaluates_iff inputs.sameIds).mpr
    (Core.runStateful_evaluation_sound execution)

/-- Raw selected-path success alone does not establish the whole static gate.
Conversely, whole typing alone supplies no actual runtime-world validity. -/
theorem runApplication?_done_iff_typed_evaluation {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type ∧
      LocalFunctionApplicationEvaluates inputs.names inputs.environment
        initialStore source value finalStore := by
  constructor
  · rintro ⟨fuel, result⟩
    obtain ⟨core, checked, _⟩ := runApplication?_eq_some_iff.mp result
    exact ⟨checkApplication?_iff_hasType.mp ⟨core, checked⟩, runApplication?_done_sound result⟩
  · rintro ⟨typing, evaluation⟩
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    obtain ⟨fuel, execution⟩ := Core.evaluation_runStateful_complete
      ((elaboration.evaluates_iff inputs.sameIds).mp evaluation)
    exact ⟨fuel, runApplication?_eq_some_iff.mpr
      ⟨core, checkApplication?_iff_elaborates.mpr elaboration, execution⟩⟩

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsApplicationCostProperties`
-/

/-! Exact actual costs require whole-call typing. Resumption instead starts
from the genuine checked exhaustion result and retains every runtime outcome. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runApplication?_done_iff_of_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost) :
    inputs.runApplication? fuel source initialStore = some (type, .done value finalStore) ↔
      cost ≤ fuel := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have checked : inputs.checkApplication? source = some (core, type) := elaboration.complete
  have path := evaluation.toSteps elaboration inputs.sameIds
  simpa [runApplication?, checked] using path.runStateful_done_iff (fuel := fuel)

theorem runApplication?_outOfFuel_iff_of_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost) :
    (∃ checkpoint, inputs.runApplication? fuel source initialStore =
      some (type, .outOfFuel checkpoint)) ↔ fuel < cost := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have checked : inputs.checkApplication? source = some (core, type) := elaboration.complete
  have path := evaluation.toSteps elaboration inputs.sameIds
  simpa [runApplication?, checked] using path.runStateful_outOfFuel_iff (fuel := fuel)

theorem runApplication?_done_iff_typed_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    inputs.runApplication? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type ∧
        ∃ cost, LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
          initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, run⟩ := runApplication?_eq_some_iff.mp completed
    have elaboration := checkApplication?_iff_elaborates.mp checked
    obtain ⟨cost, enough, path⟩ := Core.runStateful_sound run
    exact ⟨elaboration.hasType, cost,
      (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr path, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact (runApplication?_done_iff_of_cost typing evaluation).mpr enough

/-- The successful checker is recovered from the actual exhausted result;
no extra caller-supplied typing or replacement checkpoint is needed. -/
theorem runApplication?_residual_of_outOfFuel
    {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost)
    {type : Core.Ty} {spent : Nat} {checkpoint : Core.State}
    (exhausted : inputs.runApplication? spent source initialStore =
      some (type, .outOfFuel checkpoint)) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) := by
  obtain ⟨core, checked, stopped⟩ := runApplication?_eq_some_iff.mp exhausted
  have elaboration := checkApplication?_iff_elaborates.mp checked
  exact (evaluation.toSteps elaboration inputs.sameIds).residual_of_outOfFuel stopped

/-- Preserve the same static tag and the complete resumed result, including
faults or further exhaustion. This is not a restart of the source expression. -/
theorem runApplication?_resume
    {inputs : LocalInputs} {source : Syntax.Expr} {store : Core.Store}
    {type : Core.Ty} {spent : Nat} {checkpoint : Core.State}
    (exhausted : inputs.runApplication? spent source store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runApplication? (spent + additional) source store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, stopped⟩ := runApplication?_eq_some_iff.mp exhausted
  exact runApplication?_eq_some_iff.mpr
    ⟨core, checked, (Core.runStateful_resume stopped additional).symm⟩

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsApplicationRuntimeProperties`
-/

/-! Runtime-world guarantees for the same actual values and store consumed by
the separate application endpoint. Structural input records do not replace
these premises; all outcomes retain the checked static type tag. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runApplication?_runtime_done_sound
    {inputs : LocalInputs} {source : Syntax.Expr} {fuel : Nat}
    {world : Core.StoreTyping} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world initialStore)
    (result : inputs.runApplication? fuel source initialStore = some (type, .done value finalStore)) :
    LocalFunctionApplicationEvaluates inputs.names inputs.environment initialStore source value finalStore ∧
      ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.StoreHasTypes finalWorld finalStore ∧
        Core.RuntimeValueHasType finalWorld value type := by
  obtain ⟨core, checked, execution⟩ := runApplication?_eq_some_iff.mp result
  exact elaborateLocalFunctionApplication?_runtime_run_done_sound checked inputs.sameIds
    environmentTyped storeTyped execution

/-- Actual runtime-world typing supplies successful evaluation and an exact
cost for these inputs. Both fuel thresholds retain the same value and store. -/
theorem runApplication?_runtime_has_exact_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment store source value finalStore cost ∧
      ∀ fuel, (inputs.runApplication? fuel source store = some (type, .done value finalStore) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.runApplication? fuel source store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation⟩ :=
    typing.runtime_evaluates inputs.sameIds environmentTyped storeTyped
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, evaluation,
    fun fuel => ⟨runApplication?_done_iff_of_cost typing evaluation (fuel := fuel),
      runApplication?_outOfFuel_iff_of_cost typing evaluation (fuel := fuel)⟩⟩

theorem runApplication?_runtime_never_faults
    {inputs : LocalInputs} {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world
      (Resolved.LocalScope.values inputs.environment) (Resolved.LocalScope.values inputs.context))
    (storeTyped : Core.StoreHasTypes world store)
    (source : Syntax.Expr) (fuel : Nat) (type : Core.Ty)
    (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runApplication? fuel source store ≠ some (type, .fault error faultState) := by
  intro result
  obtain ⟨core, checked, fault⟩ := runApplication?_eq_some_iff.mp result
  have elaboration := checkApplication?_iff_elaborates.mp checked
  exact elaboration.runtime_run_never_faults environmentTyped storeTyped
    (.nil : Core.ContinuationHasType world [] type type) fuel error faultState fault

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionCostExecutionProperties`
-/

/-! Exact completion and exhaustion boundaries for independently costed source
evaluation. Checking remains explicit at executable frontend boundaries; raw
evaluation alone cannot discharge an unresolved or untypable skipped branch. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.runStateful_done_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.toSteps resolution lowered).runStateful_done_iff

theorem LocalExpressionEvaluatesWithCost.runStateful_outOfFuel_iff
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.toSteps resolution lowered).runStateful_outOfFuel_iff

theorem LocalExpressionEvaluatesWithCost.checked_toSteps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have runtimeLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact lowered
  exact evaluation.toSteps resolution runtimeLowered

theorem LocalExpressionEvaluatesWithCost.checked_runStateful_done_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem LocalExpressionEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

/-- The supplied runtime environment need not be typed when reflecting an
actual completed run; its identity order must match the checked lowering. -/
theorem elaborateLocalExpression?_run_done_iff_cost
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .done value finalStore ↔
      ∃ cost, LocalExpressionEvaluatesWithCost table environment
        initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨evaluation, _⟩ := elaborateLocalExpression?_run_done_sound accepted sameIds completed
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

/-- Typed aligned inputs supply a cost, a typed result, and both exact fuel
boundaries. No store-typing premise or additional terminal transition is used. -/
theorem elaborateLocalExpression?_typed_cost_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value cost, LocalExpressionEvaluatesWithCost table environment store source value store cost ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values environment) store) = .done value store ↔ cost ≤ fuel) ∧
        ((∃ suspended, Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values environment) store) = .outOfFuel suspended) ↔ fuel < cost) := by
  have typing := localExpressionHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluation.exists_cost
  exact ⟨value, cost, costed, valueTyped, fun _ =>
    ⟨costed.checked_runStateful_done_iff accepted sameIds,
      costed.checked_runStateful_outOfFuel_iff accepted sameIds⟩⟩

namespace LocalInputs

/-- Whole source typing is retained even when the supplied raw cost derivation
can skip an unresolved or untypable branch. -/
theorem run?_done_iff_typed_cost {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.run? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := run?_eq_some_iff.mp completed
    exact ⟨check?_iff_hasType.mp ⟨core, checked⟩,
      (elaborateLocalExpression?_run_done_iff_cost checked inputs.sameIds).mp execution⟩
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
    exact run?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked inputs.sameIds).mpr enough⟩

theorem typed_cost_execution {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType inputs.names inputs.context source type) (store : Core.Store) :
    ∃ value cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        store source value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.run? fuel source store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.run? fuel source store = some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := check?_iff_hasType.mpr typing
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    elaborateLocalExpression?_typed_cost_execution checked inputs.sameIds inputs.environmentTyped store
  refine ⟨value, cost, costed, valueTyped, fun fuel => ?_⟩
  simpa only [run?, checked, bind, Option.bind_some, pure, Option.some.injEq,
    Prod.mk.injEq, true_and] using boundaries fuel

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalInputsCostInvariance`
-/

/-! Same-fuel observations survive insertion of an unused typed input.
Completed type, value, and stores agree; exhausted states are deliberately
quantified separately because their Core indices and environments can differ. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Present exhaustion is exactly whole source typing together with a
successful independent cost larger than the supplied fuel. Check failure
cannot satisfy either side, even when a raw evaluation skips the bad branch. -/
theorem LocalInputs.run?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.run? fuel source store = some (type, .outOfFuel suspended)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ value cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        store source value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := LocalInputs.run?_eq_some_iff.mp exhausted
    have typing := LocalInputs.check?_iff_hasType.mp ⟨core, checked⟩
    obtain ⟨value, cost, costed, _, boundaries⟩ := LocalInputs.typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := LocalInputs.check?_iff_hasType.mpr typing
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, LocalInputs.run?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unlike existential sufficient-fuel agreement, this law uses the very same
fuel on both sides and retains the completed type, value, and both stores. -/
theorem AvoidsLocalName.bindFresh_run_done_at_fuel_iff
    {name : String} {source : Syntax.Expr} (avoids : AvoidsLocalName name source)
    (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source initialStore =
        some (type, .done value finalStore) ↔
      inputs.run? fuel source initialStore = some (type, .done value finalStore) := by
  rw [LocalInputs.run?_done_iff_typed_cost, LocalInputs.run?_done_iff_typed_cost]
  refine and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped) ?_
  exact exists_congr fun _ =>
    and_congr (avoids.bindFresh_cost_iff inputs owner newType newValue valueTyped) Iff.rfl

/-- Only exhaustion presence is compared. The old and new suspended states
are separate witnesses, with no equality or shared-state premise. -/
theorem AvoidsLocalName.bindFresh_run_outOfFuel_iff
    {name : String} {source : Syntax.Expr} (avoids : AvoidsLocalName name source)
    (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ newSuspended, (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source store =
        some (type, .outOfFuel newSuspended)) ↔
      ∃ oldSuspended, inputs.run? fuel source store = some (type, .outOfFuel oldSuspended) := by
  rw [LocalInputs.run?_outOfFuel_iff_typed_cost, LocalInputs.run?_outOfFuel_iff_typed_cost]
  refine and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped) ?_
  exact exists_congr fun _ => exists_congr fun _ =>
    and_congr (avoids.bindFresh_cost_iff inputs owner newType newValue valueTyped) Iff.rfl

end Solcore.Frontend
