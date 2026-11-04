import Solcore.Core.Internal.Preservation
import Solcore.Core.RuntimeTyping
import Solcore.Core.Correspondence
import Solcore.Core.Fuel

/-!
# Type preservation and finite execution safety

Main theorems. `evaluation_preserves_type` is preservation for `Evaluates`. `transition_preserves_state_type`
and `state_progress` are preservation and progress for the machine, and `Steps.preserve_state_type`
and `well_typed_state_never_faults` follow.

For a program that passes `Program.check`, with any fuel: `Program.checked_run_never_faults` and
`Program.checked_runStateful_never_faults` exclude `MachineFault`,
`Program.checked_run_preserves_result_type` gives the value its type,
`Program.checked_runStateful_has_type` covers every result, including fuel checkpoints, and
`well_typed_runStateful_resume_has_type` covers resuming one. `Program.checked_run_completes` and
`Program.checked_run_has_sufficient_fuel` turn an evaluation into a completed run.
-/

section
-- leanmerge: from Solcore.Core.Safety
/-! ## Preservation for the state-threaded evaluator -/

set_option autoImplicit false

namespace Solcore.Core

theorem evaluation_preserves_type
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store}
    {expr : Expr} {value : Value} {type : Ty} {world : StoreTyping}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (typing : HasType context expr type definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : RuntimeStoreHasTypes world initialStore definitions) :
    ∃ finalWorld,
      WorldExtends world finalWorld ∧
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value type definitions := by
  induction evaluation generalizing context type world with
  | unit =>
      cases typing
      exact ⟨world, .refl world, storeTyping, .unit⟩
  | bool =>
      cases typing
      exact ⟨world, .refl world, storeTyping, .bool⟩
  | word =>
      cases typing
      exact ⟨world, .refl world, storeTyping, .word⟩
  | integer =>
      cases typing
      exact ⟨world, .refl world, storeTyping, .integer⟩
  | pair _ _ leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          obtain ⟨leftWorld, leftExtension, leftStoreTyping, leftValueTyping⟩ :=
            leftIH leftTyping environmentTyping storeTyping
          obtain ⟨rightWorld, rightExtension, rightStoreTyping, rightValueTyping⟩ :=
            rightIH rightTyping
              (environmentTyping.weaken leftExtension) leftStoreTyping
          exact ⟨rightWorld, leftExtension.trans rightExtension,
            rightStoreTyping,
            .pair (leftValueTyping.weaken rightExtension) rightValueTyping⟩
  | first _ operandIH =>
      cases typing with
      | first operandTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, valueTyping⟩ :=
            operandIH operandTyping environmentTyping storeTyping
          cases valueTyping with
          | pair leftTyping _ =>
              exact ⟨resultWorld, extension, resultStoreTyping, leftTyping⟩
  | second _ operandIH =>
      cases typing with
      | second operandTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, valueTyping⟩ :=
            operandIH operandTyping environmentTyping storeTyping
          cases valueTyping with
          | pair _ rightTyping =>
              exact ⟨resultWorld, extension, resultStoreTyping, rightTyping⟩
  | inLeft _ payloadIH =>
      cases typing with
      | inLeft _ payloadTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, valueTyping⟩ :=
            payloadIH payloadTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping, .inLeft valueTyping⟩
  | inRight _ payloadIH =>
      cases typing with
      | inRight _ payloadTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, valueTyping⟩ :=
            payloadIH payloadTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping, .inRight valueTyping⟩
  | caseLeft _ _ scrutineeIH branchIH =>
      cases typing with
      | caseE scrutineeTyping leftTyping _ =>
          obtain ⟨branchWorld, scrutineeExtension, branchStoreTyping,
            scrutineeValueTyping⟩ :=
              scrutineeIH scrutineeTyping environmentTyping storeTyping
          cases scrutineeValueTyping with
          | inLeft payloadTyping =>
              obtain ⟨resultWorld, branchExtension, resultStoreTyping,
                resultTyping⟩ :=
                  branchIH leftTyping
                    (.cons payloadTyping
                      (environmentTyping.weaken scrutineeExtension))
                    branchStoreTyping
              exact ⟨resultWorld, scrutineeExtension.trans branchExtension,
                resultStoreTyping, resultTyping⟩
  | caseRight _ _ scrutineeIH branchIH =>
      cases typing with
      | caseE scrutineeTyping _ rightTyping =>
          obtain ⟨branchWorld, scrutineeExtension, branchStoreTyping,
            scrutineeValueTyping⟩ :=
              scrutineeIH scrutineeTyping environmentTyping storeTyping
          cases scrutineeValueTyping with
          | inRight payloadTyping =>
              obtain ⟨resultWorld, branchExtension, resultStoreTyping,
                resultTyping⟩ :=
                  branchIH rightTyping
                    (.cons payloadTyping
                      (environmentTyping.weaken scrutineeExtension))
                    branchStoreTyping
              exact ⟨resultWorld, scrutineeExtension.trans branchExtension,
                resultStoreTyping, resultTyping⟩
  | lambda =>
      cases typing with
      | lambda _ _ bodyTyping =>
          exact ⟨world, .refl world, storeTyping,
            .closure environmentTyping bodyTyping⟩
  | apply _ _ _ functionIH argumentIH bodyIH =>
      cases typing with
      | apply functionTyping argumentTyping =>
          obtain ⟨functionWorld, functionExtension, functionStoreTyping,
            functionValueTyping⟩ :=
              functionIH functionTyping environmentTyping storeTyping
          cases functionValueTyping with
          | closure capturedTyping bodyTyping =>
              obtain ⟨argumentWorld, argumentExtension, argumentStoreTyping,
                argumentValueTyping⟩ :=
                  argumentIH argumentTyping
                    (environmentTyping.weaken functionExtension)
                    functionStoreTyping
              obtain ⟨resultWorld, bodyExtension, resultStoreTyping,
                resultTyping⟩ :=
                  bodyIH bodyTyping
                    (.cons argumentValueTyping
                      (capturedTyping.weaken argumentExtension))
                    argumentStoreTyping
              exact ⟨resultWorld,
                functionExtension.trans (argumentExtension.trans bodyExtension),
                resultStoreTyping, resultTyping⟩
  | var valueLookup =>
      cases typing with
      | var typeLookup =>
          obtain ⟨found, foundLookup, foundTyping⟩ :=
            environmentTyping.lookup typeLookup
          rw [valueLookup] at foundLookup
          cases foundLookup
          exact ⟨world, .refl world, storeTyping, foundTyping⟩
  | @newCell _ _ initializedStore elementType _ initialValue _ initializerIH =>
      cases typing with
      | newCell initializerTyping =>
          obtain ⟨initializedWorld, initializerExtension,
            initializedStoreTyping, initialValueTyping⟩ :=
              initializerIH initializerTyping environmentTyping storeTyping
          let resultWorld := initializedWorld ++ [elementType]
          have resultStoreTyping :
              RuntimeStoreHasTypes resultWorld
                (initializedStore.allocate initialValue).1 definitions := by
            simpa [resultWorld] using
              initializedStoreTyping.allocate initialValueTyping
          have freshLookup :
              resultWorld[(initializedStore.allocate initialValue).2]? =
                some elementType := by
            simp [resultWorld, ← initializedStoreTyping.length_eq]
          exact ⟨resultWorld,
            initializerExtension.trans ⟨[elementType], rfl⟩,
            resultStoreTyping, .cellRef freshLookup⟩
  | loadCell _ loaded referenceIH =>
      cases typing with
      | loadCell referenceTyping =>
          obtain ⟨referenceWorld, extension, referenceStoreTyping,
            referenceValueTyping⟩ :=
              referenceIH referenceTyping environmentTyping storeTyping
          cases referenceValueTyping with
          | cellRef found =>
              obtain ⟨storedValue, storedLookup, storedTyping⟩ :=
                referenceStoreTyping.lookup found
              rw [loaded] at storedLookup
              cases storedLookup
              exact ⟨referenceWorld, extension, referenceStoreTyping,
                storedTyping⟩
  | storeCell _ _ _ written referenceIH valueIH =>
      cases typing with
      | storeCell referenceTyping valueTyping =>
          obtain ⟨referenceWorld, referenceExtension, referenceStoreTyping,
            referenceValueTyping⟩ :=
              referenceIH referenceTyping environmentTyping storeTyping
          cases referenceValueTyping with
          | cellRef found =>
              obtain ⟨valueWorld, valueExtension, valueStoreTyping,
                newValueTyping⟩ :=
                  valueIH valueTyping
                    (environmentTyping.weaken referenceExtension)
                    referenceStoreTyping
              have futureFound := valueExtension.lookup found
              have resultStoreTyping :=
                valueStoreTyping.write futureFound newValueTyping written
              exact ⟨valueWorld, referenceExtension.trans valueExtension,
                resultStoreTyping, .unit⟩
  | construct _ payloadIH =>
      cases typing with
      | construct constructorLookup payloadTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping,
            payloadValueTyping⟩ :=
              payloadIH payloadTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping,
            .constructed constructorLookup payloadValueTyping⟩
  | matchData _ ownerEq branchLookup _ scrutineeIH branchIH =>
      cases typing with
      | matchData definitionLookup _ scrutineeTyping branchesTyping =>
          obtain ⟨branchWorld, scrutineeExtension, branchStoreTyping,
            scrutineeValueTyping⟩ :=
              scrutineeIH scrutineeTyping environmentTyping storeTyping
          cases scrutineeValueTyping with
          | constructed constructorLookup payloadTyping =>
              obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
                payloadTypeLookup⟩ :=
                  DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                    constructorLookup
              rw [ownerEq] at runtimeDefinitionLookup
              change definitions[_]? = some _ at definitionLookup
              rw [definitionLookup] at runtimeDefinitionLookup
              cases runtimeDefinitionLookup
              have branchTyping :=
                branchesTyping.lookup payloadTypeLookup branchLookup
              obtain ⟨resultWorld, branchExtension, resultStoreTyping,
                resultTyping⟩ :=
                  branchIH branchTyping
                    (.cons payloadTyping
                      (environmentTyping.weaken scrutineeExtension))
                    branchStoreTyping
              exact ⟨resultWorld, scrutineeExtension.trans branchExtension,
                resultStoreTyping, resultTyping⟩
  | unary _ applied operandIH =>
      cases typing with
      | unary operandTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, _⟩ :=
            operandIH operandTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping,
            unary_apply_result_has_runtime_type applied
              (definitions := definitions)⟩
  | binary _ _ applied leftIH rightIH =>
      cases typing with
      | binary leftTyping rightTyping =>
          obtain ⟨rightWorld, leftExtension, rightStoreTyping, _⟩ :=
            leftIH leftTyping environmentTyping storeTyping
          obtain ⟨resultWorld, rightExtension, resultStoreTyping, _⟩ :=
            rightIH rightTyping
              (environmentTyping.weaken leftExtension) rightStoreTyping
          exact ⟨resultWorld, leftExtension.trans rightExtension,
            resultStoreTyping,
            binary_apply_result_has_runtime_type applied
              (definitions := definitions)⟩
  | ternary _ _ _ applied firstIH secondIH thirdIH =>
      cases typing with
      | ternary firstTyping secondTyping thirdTyping =>
          obtain ⟨secondWorld, firstExtension, secondStoreTyping, _⟩ :=
            firstIH firstTyping environmentTyping storeTyping
          obtain ⟨thirdWorld, secondExtension, thirdStoreTyping, _⟩ :=
            secondIH secondTyping
              (environmentTyping.weaken firstExtension) secondStoreTyping
          obtain ⟨resultWorld, thirdExtension, resultStoreTyping, _⟩ :=
            thirdIH thirdTyping
              (environmentTyping.weaken
                (firstExtension.trans secondExtension))
              thirdStoreTyping
          exact ⟨resultWorld,
            (firstExtension.trans secondExtension).trans thirdExtension,
            resultStoreTyping,
            ternary_apply_result_has_runtime_type applied
              (definitions := definitions)⟩
  | letE _ _ boundIH bodyIH =>
      cases typing with
      | letE boundTyping bodyTyping =>
          obtain ⟨bodyWorld, boundExtension, bodyStoreTyping, boundValueTyping⟩ :=
            boundIH boundTyping environmentTyping storeTyping
          obtain ⟨resultWorld, bodyExtension, resultStoreTyping, resultTyping⟩ :=
            bodyIH bodyTyping
              (.cons boundValueTyping (environmentTyping.weaken boundExtension))
              bodyStoreTyping
          exact ⟨resultWorld, boundExtension.trans bodyExtension,
            resultStoreTyping, resultTyping⟩
  | ifTrue _ _ conditionIH branchIH =>
      cases typing with
      | ifE conditionTyping thenTyping _ =>
          obtain ⟨branchWorld, conditionExtension, branchStoreTyping, _⟩ :=
            conditionIH conditionTyping environmentTyping storeTyping
          obtain ⟨resultWorld, branchExtension, resultStoreTyping, resultTyping⟩ :=
            branchIH thenTyping (environmentTyping.weaken conditionExtension)
              branchStoreTyping
          exact ⟨resultWorld, conditionExtension.trans branchExtension,
            resultStoreTyping, resultTyping⟩
  | ifFalse _ _ conditionIH branchIH =>
      cases typing with
      | ifE conditionTyping _ elseTyping =>
          obtain ⟨branchWorld, conditionExtension, branchStoreTyping, _⟩ :=
            conditionIH conditionTyping environmentTyping storeTyping
          obtain ⟨resultWorld, branchExtension, resultStoreTyping, resultTyping⟩ :=
            branchIH elseTyping (environmentTyping.weaken conditionExtension)
              branchStoreTyping
          exact ⟨resultWorld, conditionExtension.trans branchExtension,
            resultStoreTyping, resultTyping⟩

/-! ## Typed finite evaluations -/

/-- A known finite evaluation has a typed result in an extending runtime world.
General cells permit recursive closures, so typing alone supplies no evaluation. -/
theorem well_typed_evaluates
    {definitions : DataEnvironment}
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type definitions)
    {world : StoreTyping} {environment : Environment} {store finalStore : Store}
    {value : Value}
    (evaluation : Evaluates environment store expr value finalStore)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : RuntimeStoreHasTypes world store definitions) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      Evaluates environment store expr value finalStore ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, extension, finalTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluation typing environmentTyping storeTyping
  exact ⟨finalWorld, finalStore, value, extension, finalTyped, evaluation, valueTyped⟩

theorem closed_well_typed_evaluates
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ finalWorld finalStore value,
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      Evaluates [] [] expr value finalStore ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, finalStore, value, _, finalStoreTyping,
    evaluation, valueTyping⟩ :=
      well_typed_evaluates typing evaluation .nil (RuntimeStoreHasTypes.nil definitions)
  exact ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩

/-- A concrete finite semantic execution yields a typed machine completion. -/
theorem closed_well_typed_runStateful_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing evaluation
  obtain ⟨fuel, result⟩ := evaluation_runStateful_complete evaluation
  exact ⟨fuel, finalWorld, finalStore, value, result,
    finalStoreTyping, valueTyping⟩

theorem closed_well_typed_run_stateful_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value type definitions :=
  closed_well_typed_runStateful_completes typing evaluation

/-- The sufficient budget comes from a finite semantic execution, not typing. -/
theorem closed_well_typed_runStateful_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ required finalWorld finalStore value,
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value type definitions ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing evaluation
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, finalWorld, finalStore, value,
    finalStoreTyping, valueTyping, completes⟩

theorem closed_well_typed_run_stateful_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ required finalWorld finalStore value,
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value type definitions ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore :=
  closed_well_typed_runStateful_has_sufficient_fuel typing evaluation

theorem closed_well_typed_run_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ fuel value,
      run fuel (State.initial expr) = .done value ∧
      ValueHasType value type definitions := by
  obtain ⟨fuel, finalWorld, finalStore, value, result, _, valueTyping⟩ :=
    closed_well_typed_runStateful_completes typing evaluation
  exact ⟨fuel, value,
    by simp [run, result, StatefulRunResult.erase], valueTyping.erase⟩

theorem closed_well_typed_run_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore) :
    ∃ required value,
      ValueHasType value type definitions ∧
      ∀ fuel, required ≤ fuel →
        run fuel (State.initial expr) = .done value := by
  obtain ⟨required, finalWorld, finalStore, value, _, valueTyping,
    completes⟩ :=
      closed_well_typed_runStateful_has_sufficient_fuel
        typing evaluation
  exact ⟨required, value, valueTyping.erase, fun fuel enough => by
    simp [run, completes fuel enough, StatefulRunResult.erase]⟩

theorem transition_preserves_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType definitions)
    (transition : Transition state next) :
    StateHasType next resultType definitions := by
  cases transition with
  | unit =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret storeTyping .unit continuationTyping
  | bool =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret storeTyping .bool continuationTyping
  | word =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret storeTyping .word continuationTyping
  | integer =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret storeTyping .integer continuationTyping
  | enterPair =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | pair leftTyping rightTyping =>
              exact .eval storeTyping environmentTyping leftTyping
                (.cons (.pairRight environmentTyping rightTyping)
                  continuationTyping)
  | enterPairRight =>
      cases stateTyping with
      | ret storeTyping leftTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | pairRight environmentTyping rightTyping =>
                  exact .eval storeTyping environmentTyping rightTyping
                    (.cons (.pairApply leftTyping) restTyping)
  | applyPair =>
      cases stateTyping with
      | ret storeTyping rightTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | pairApply leftTyping =>
                  exact .ret storeTyping (.pair leftTyping rightTyping) restTyping
  | enterFirst =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | first operandTyping =>
              exact .eval storeTyping environmentTyping operandTyping
                (.cons .firstApply continuationTyping)
  | applyFirst =>
      cases stateTyping with
      | ret storeTyping pairTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | firstApply =>
                  cases pairTyping with
                  | pair leftTyping _ =>
                      exact .ret storeTyping leftTyping restTyping
  | enterSecond =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | second operandTyping =>
              exact .eval storeTyping environmentTyping operandTyping
                (.cons .secondApply continuationTyping)
  | applySecond =>
      cases stateTyping with
      | ret storeTyping pairTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | secondApply =>
                  cases pairTyping with
                  | pair _ rightTyping =>
                      exact .ret storeTyping rightTyping restTyping
  | enterInLeft =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | inLeft _ payloadTyping =>
              exact .eval storeTyping environmentTyping payloadTyping
                (.cons .inLeftApply continuationTyping)
  | applyInLeft =>
      cases stateTyping with
      | ret storeTyping payloadTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | inLeftApply =>
                  exact .ret storeTyping (.inLeft payloadTyping) restTyping
  | enterInRight =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | inRight _ payloadTyping =>
              exact .eval storeTyping environmentTyping payloadTyping
                (.cons .inRightApply continuationTyping)
  | applyInRight =>
      cases stateTyping with
      | ret storeTyping payloadTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | inRightApply =>
                  exact .ret storeTyping (.inRight payloadTyping) restTyping
  | enterCase =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | caseE scrutineeTyping leftTyping rightTyping =>
              exact .eval storeTyping environmentTyping scrutineeTyping
                (.cons
                  (.caseBranches environmentTyping leftTyping rightTyping)
                  continuationTyping)
  | chooseLeft =>
      cases stateTyping with
      | ret storeTyping sumTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | caseBranches environmentTyping leftTyping rightTyping =>
                  cases sumTyping with
                  | inLeft payloadTyping =>
                      exact .eval storeTyping
                        (.cons payloadTyping environmentTyping)
                        leftTyping restTyping
  | chooseRight =>
      cases stateTyping with
      | ret storeTyping sumTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | caseBranches environmentTyping leftTyping rightTyping =>
                  cases sumTyping with
                  | inRight payloadTyping =>
                      exact .eval storeTyping
                        (.cons payloadTyping environmentTyping)
                        rightTyping restTyping
  | enterNewCell =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | newCell initializerTyping =>
              exact .eval storeTyping environmentTyping initializerTyping
                (.cons .newCellApply continuationTyping)
  | @applyNewCell elementType initialValue continuation store =>
      cases stateTyping with
      | @ret _ world _ _ _ _ _ storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | @newCellApply _ elementType =>
                  let futureWorld := world ++ [elementType]
                  have extension : WorldExtends world futureWorld :=
                    ⟨[elementType], rfl⟩
                  have futureStoreTyping :
                      RuntimeStoreHasTypes futureWorld (store.allocate initialValue).1 definitions := by
                    simpa [futureWorld] using
                      storeTyping.allocate valueTyping
                  have fresh :
                      futureWorld[(store.allocate initialValue).2]? =
                        some elementType := by
                    simp [futureWorld, Store.allocate, ← storeTyping.length_eq]
                  exact .ret futureStoreTyping (.cellRef fresh)
                    (restTyping.weaken extension)
  | enterLoadCell =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | loadCell referenceTyping =>
              exact .eval storeTyping environmentTyping referenceTyping
                (.cons .loadCellApply continuationTyping)
  | applyLoadCell loaded =>
      cases stateTyping with
      | ret storeTyping cellTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | loadCellApply =>
                  cases cellTyping with
                  | cellRef found =>
                      obtain ⟨stored, storedRead, storedTyping⟩ :=
                        storeTyping.lookup found
                      rw [loaded] at storedRead
                      cases storedRead
                      exact .ret storeTyping
                        storedTyping
                        restTyping
  | enterStoreCell =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | storeCell referenceTyping valueTyping =>
              exact .eval storeTyping environmentTyping referenceTyping
                (.cons
                  (.storeCellValue environmentTyping valueTyping)
                  continuationTyping)
  | beginStoreCellValue _ =>
      cases stateTyping with
      | ret storeTyping cellTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | storeCellValue environmentTyping valueTyping =>
                  cases cellTyping with
                  | cellRef found =>
                      exact .eval storeTyping environmentTyping valueTyping
                        (.cons (.storeCellApply found) restTyping)
  | applyStoreCell written =>
      cases stateTyping with
      | ret storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | storeCellApply found =>
                  exact .ret
                    (storeTyping.write found valueTyping written)
                    .unit restTyping
  | enterConstruct =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | construct constructorLookup payloadTyping =>
              exact .eval storeTyping environmentTyping payloadTyping
                (.cons (.constructApply constructorLookup) continuationTyping)
  | applyConstruct =>
      cases stateTyping with
      | ret storeTyping payloadTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | constructApply constructorLookup =>
                  exact .ret storeTyping
                    (.constructed constructorLookup payloadTyping) restTyping
  | enterMatchData =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | matchData definitionLookup _ scrutineeTyping branchesTyping =>
              exact .eval storeTyping environmentTyping scrutineeTyping
                (.cons
                  (.matchDataApply definitionLookup environmentTyping
                    branchesTyping)
                  continuationTyping)
  | chooseData ownerEq branchLookup =>
      cases stateTyping with
      | ret storeTyping dataTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | matchDataApply definitionLookup environmentTyping branchesTyping =>
                  cases dataTyping with
                  | constructed constructorLookup payloadTyping =>
                      obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
                        payloadTypeLookup⟩ :=
                          DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                            constructorLookup
                      rw [ownerEq] at runtimeDefinitionLookup
                      have typedDefinitionLookup :=
                        DataEnvironment.lookupDataType?_eq_some_iff.mp
                          definitionLookup
                      rw [typedDefinitionLookup] at runtimeDefinitionLookup
                      cases runtimeDefinitionLookup
                      exact .eval storeTyping
                        (.cons payloadTyping environmentTyping)
                        (branchesTyping.lookup payloadTypeLookup branchLookup)
                        restTyping
  | lambda =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | lambda _ _ bodyTyping =>
              exact .ret storeTyping
                (.closure environmentTyping bodyTyping) continuationTyping
  | enterApply =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | apply functionTyping argumentTyping =>
              exact .eval storeTyping environmentTyping functionTyping
                (.cons
                  (.applyArgument environmentTyping argumentTyping)
                  continuationTyping)
  | beginArgument =>
      cases stateTyping with
      | ret storeTyping functionTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyArgument callerEnvironmentTyping argumentTyping =>
                  cases functionTyping with
                  | closure capturedEnvironmentTyping bodyTyping =>
                      exact .eval storeTyping callerEnvironmentTyping
                        argumentTyping
                        (.cons
                          (.applyClosure capturedEnvironmentTyping bodyTyping)
                          restTyping)
  | invokeClosure =>
      cases stateTyping with
      | ret storeTyping argumentTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyClosure capturedEnvironmentTyping bodyTyping =>
                  exact .eval storeTyping
                    (.cons argumentTyping capturedEnvironmentTyping)
                    bodyTyping restTyping
  | var valueLookup =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | var typeLookup =>
              obtain ⟨found, foundLookup, foundTyping⟩ :=
                environmentTyping.lookup typeLookup
              rw [valueLookup] at foundLookup
              cases foundLookup
              exact .ret storeTyping foundTyping continuationTyping
  | enterUnary =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | unary operandTyping =>
              exact .eval storeTyping environmentTyping operandTyping
                (.cons .unaryApply continuationTyping)
  | applyUnary applied =>
      cases stateTyping with
      | ret storeTyping operandTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | unaryApply =>
                  exact .ret storeTyping
                    (unary_apply_result_has_runtime_type
                      (definitions := definitions) applied) restTyping
  | enterBinary =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | binary leftTyping rightTyping =>
              exact .eval storeTyping environmentTyping leftTyping
                (.cons (.binaryRight environmentTyping rightTyping)
                  continuationTyping)
  | enterBinaryRight =>
      cases stateTyping with
      | ret storeTyping leftTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | binaryRight environmentTyping rightTyping =>
                  exact .eval storeTyping environmentTyping rightTyping
                    (.cons (.binaryApply leftTyping) restTyping)
  | applyBinary applied =>
      cases stateTyping with
      | ret storeTyping rightTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | binaryApply leftTyping =>
                  exact .ret storeTyping
                    (binary_apply_result_has_runtime_type
                      (definitions := definitions) applied) restTyping
  | enterTernary =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | ternary firstTyping secondTyping thirdTyping =>
              exact .eval storeTyping environmentTyping firstTyping
                (.cons
                  (.ternarySecond environmentTyping secondTyping thirdTyping)
                  continuationTyping)
  | enterTernarySecond =>
      cases stateTyping with
      | ret storeTyping firstTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ternarySecond environmentTyping secondTyping thirdTyping =>
                  exact .eval storeTyping environmentTyping secondTyping
                    (.cons (.ternaryThird firstTyping environmentTyping thirdTyping)
                      restTyping)
  | enterTernaryThird =>
      cases stateTyping with
      | ret storeTyping secondTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ternaryThird firstTyping environmentTyping thirdTyping =>
                  exact .eval storeTyping environmentTyping thirdTyping
                    (.cons (.ternaryApply firstTyping secondTyping) restTyping)
  | applyTernary applied =>
      cases stateTyping with
      | ret storeTyping thirdTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ternaryApply firstTyping secondTyping =>
                  exact .ret storeTyping
                    (ternary_apply_result_has_runtime_type
                      (definitions := definitions) applied) restTyping
  | enterLet =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | letE boundTyping bodyTyping =>
              exact .eval storeTyping environmentTyping boundTyping
                (.cons (.letBody environmentTyping bodyTyping)
                  continuationTyping)
  | bindLet =>
      cases stateTyping with
      | ret storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | letBody environmentTyping bodyTyping =>
                  exact .eval storeTyping
                    (.cons valueTyping environmentTyping)
                    bodyTyping restTyping
  | enterIf =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | ifE conditionTyping thenTyping elseTyping =>
              exact .eval storeTyping environmentTyping conditionTyping
                (.cons
                  (.ifBranches environmentTyping thenTyping elseTyping)
                  continuationTyping)
  | chooseTrue =>
      cases stateTyping with
      | ret storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ifBranches environmentTyping thenTyping elseTyping =>
                  exact .eval storeTyping environmentTyping thenTyping restTyping
  | chooseFalse =>
      cases stateTyping with
      | ret storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ifBranches environmentTyping thenTyping elseTyping =>
                  exact .eval storeTyping environmentTyping elseTyping restTyping

theorem state_progress
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType definitions) :
    (∃ value store, state = State.final value store) ∨
      ∃ next, Transition state next := by
  cases stateTyping with
  | eval storeTyping environmentTyping exprTyping continuationTyping =>
      cases exprTyping with
      | unit => exact .inr ⟨_, .unit⟩
      | bool => exact .inr ⟨_, .bool⟩
      | word => exact .inr ⟨_, .word⟩
      | integer => exact .inr ⟨_, .integer⟩
      | var typeLookup =>
          obtain ⟨value, valueLookup, _⟩ := environmentTyping.lookup typeLookup
          exact .inr ⟨_, .var valueLookup⟩
      | pair => exact .inr ⟨_, .enterPair⟩
      | first => exact .inr ⟨_, .enterFirst⟩
      | second => exact .inr ⟨_, .enterSecond⟩
      | lambda => exact .inr ⟨_, .lambda⟩
      | apply => exact .inr ⟨_, .enterApply⟩
      | inLeft => exact .inr ⟨_, .enterInLeft⟩
      | inRight => exact .inr ⟨_, .enterInRight⟩
      | caseE => exact .inr ⟨_, .enterCase⟩
      | newCell => exact .inr ⟨_, .enterNewCell⟩
      | loadCell => exact .inr ⟨_, .enterLoadCell⟩
      | storeCell => exact .inr ⟨_, .enterStoreCell⟩
      | construct => exact .inr ⟨_, .enterConstruct⟩
      | matchData => exact .inr ⟨_, .enterMatchData⟩
      | unary => exact .inr ⟨_, .enterUnary⟩
      | binary => exact .inr ⟨_, .enterBinary⟩
      | ternary => exact .inr ⟨_, .enterTernary⟩
      | letE => exact .inr ⟨_, .enterLet⟩
      | ifE => exact .inr ⟨_, .enterIf⟩
  | @ret _ world value continuation store controlType resultType
      storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact .inl ⟨value, store, rfl⟩
      | cons frameTyping restTyping =>
          cases frameTyping with
          | unaryApply =>
              obtain ⟨result, applied, _⟩ :=
                UnaryOp.apply_total_of_type _ _ valueTyping.type_eq
              exact .inr ⟨_, .applyUnary applied⟩
          | binaryRight => exact .inr ⟨_, .enterBinaryRight⟩
          | binaryApply leftTyping =>
              obtain ⟨result, applied, _⟩ :=
                BinaryOp.apply_total_of_types _ _ _
                  leftTyping.type_eq valueTyping.type_eq
              exact .inr ⟨_, .applyBinary applied⟩
          | ternarySecond => exact .inr ⟨_, .enterTernarySecond⟩
          | ternaryThird => exact .inr ⟨_, .enterTernaryThird⟩
          | ternaryApply firstTyping secondTyping =>
              obtain ⟨result, applied, _⟩ :=
                TernaryOp.apply_total_of_types _ _ _ _
                  firstTyping.type_eq secondTyping.type_eq valueTyping.type_eq
              exact .inr ⟨_, .applyTernary applied⟩
          | pairRight => exact .inr ⟨_, .enterPairRight⟩
          | pairApply => exact .inr ⟨_, .applyPair⟩
          | firstApply =>
              cases valueTyping with
              | pair => exact .inr ⟨_, .applyFirst⟩
          | secondApply =>
              cases valueTyping with
              | pair => exact .inr ⟨_, .applySecond⟩
          | inLeftApply => exact .inr ⟨_, .applyInLeft⟩
          | inRightApply => exact .inr ⟨_, .applyInRight⟩
          | caseBranches =>
              cases valueTyping with
              | inLeft => exact .inr ⟨_, .chooseLeft⟩
              | inRight => exact .inr ⟨_, .chooseRight⟩
          | newCellApply => exact .inr ⟨_, .applyNewCell⟩
          | loadCellApply =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨loaded, read, _⟩ := storeTyping.lookup found
                  exact .inr ⟨_, .applyLoadCell read⟩
          | storeCellValue _ _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨oldValue, read, _⟩ := storeTyping.lookup found
                  exact .inr ⟨_, .beginStoreCellValue read⟩
          | storeCellApply found =>
              obtain ⟨updatedStore, written⟩ :=
                storeTyping.write_exists (value := value) found
              exact .inr ⟨_, .applyStoreCell written⟩
          | constructApply _ => exact .inr ⟨_, .applyConstruct⟩
          | matchDataApply definitionLookup _ branchesTyping =>
              cases valueTyping with
              | constructed constructorLookup payloadTyping =>
                  obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
                    payloadTypeLookup⟩ :=
                      DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                        constructorLookup
                  have typedDefinitionLookup :=
                    DataEnvironment.lookupDataType?_eq_some_iff.mp
                      definitionLookup
                  rw [typedDefinitionLookup] at runtimeDefinitionLookup
                  cases runtimeDefinitionLookup
                  obtain ⟨branch, branchLookup⟩ :=
                    branchesTyping.branch_exists payloadTypeLookup
                  exact .inr ⟨_, .chooseData rfl branchLookup⟩
          | applyArgument =>
              cases valueTyping with
              | closure => exact .inr ⟨_, .beginArgument⟩
          | applyClosure => exact .inr ⟨_, .invokeClosure⟩
          | letBody => exact .inr ⟨_, .bindLet⟩
          | ifBranches =>
              cases valueTyping with
              | bool =>
                  rename_i decision
                  cases decision with
                  | false => exact .inr ⟨_, .chooseFalse⟩
                  | true => exact .inr ⟨_, .chooseTrue⟩

theorem Steps.preserve_state_type
    {definitions : DataEnvironment}
    {steps : Nat} {start finish : State} {resultType : Ty}
    (path : Steps steps start finish)
    (startTyping : StateHasType start resultType definitions) :
    StateHasType finish resultType definitions := by
  induction path with
  | refl => exact startTyping
  | cons transition tail tailIH =>
      exact tailIH (transition_preserves_state_type startTyping transition)

theorem well_typed_state_never_faults
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType definitions) :
    advance state ≠ .fault error := by
  intro faulted
  cases state_progress stateTyping with
  | inl final =>
      obtain ⟨value, store, rfl⟩ := final
      simp [advance, State.final] at faulted
  | inr progresses =>
      obtain ⟨next, transition⟩ := progresses
      have advances := advance_next_iff.mpr transition
      rw [advances] at faulted
      contradiction

theorem initial_state_has_type
    {definitions : DataEnvironment} {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions) :
    StateHasType (State.initial expr) type definitions :=
  .eval (RuntimeStoreHasTypes.nil definitions) .nil typing .nil

theorem well_typed_runStateful_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {state faultState : State}
    {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType definitions) :
    runStateful fuel state ≠ .fault error faultState := by
  intro faulted
  obtain ⟨steps, _, path, terminal⟩ := runStateful_fault_sound faulted
  exact well_typed_state_never_faults
    (path.preserve_state_type stateTyping) terminal

theorem well_typed_run_stateful_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {state faultState : State}
    {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType definitions) :
    runStateful fuel state ≠ .fault error faultState :=
  well_typed_runStateful_never_faults stateTyping

theorem well_typed_runStateful_preserves_result_type
    {definitions : DataEnvironment}
    {fuel : Nat} {state : State} {resultType : Ty}
    {value : Value} {finalStore : Store}
    (stateTyping : StateHasType state resultType definitions)
    (result : runStateful fuel state = .done value finalStore) :
    ∃ finalWorld,
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value resultType definitions := by
  obtain ⟨steps, _, path⟩ := runStateful_sound result
  have finalTyping := path.preserve_state_type stateTyping
  cases finalTyping with
  | ret storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact ⟨_, storeTyping, valueTyping⟩

theorem well_typed_run_stateful_preserves_result_type
    {definitions : DataEnvironment}
    {fuel : Nat} {state : State} {resultType : Ty}
    {value : Value} {finalStore : Store}
    (stateTyping : StateHasType state resultType definitions)
    (result : runStateful fuel state = .done value finalStore) :
    ∃ finalWorld,
      RuntimeStoreHasTypes finalWorld finalStore definitions ∧
      RuntimeValueHasType finalWorld value resultType definitions :=
  well_typed_runStateful_preserves_result_type stateTyping result

theorem well_typed_run_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType definitions) :
    run fuel state ≠ .fault error := by
  intro faulted
  cases stateful : runStateful fuel state with
  | done value finalStore =>
      simp [run, stateful, StatefulRunResult.erase] at faulted
  | outOfFuel suspendedState =>
      simp [run, stateful, StatefulRunResult.erase] at faulted
  | fault actualError faultState =>
      have sameError : actualError = error := by
        simpa [run, stateful, StatefulRunResult.erase] using faulted
      subst actualError
      exact well_typed_runStateful_never_faults stateTyping stateful

theorem well_typed_run_preserves_result_type
    {definitions : DataEnvironment}
    {fuel : Nat} {state : State} {resultType : Ty} {value : Value}
    (stateTyping : StateHasType state resultType definitions)
    (result : run fuel state = .done value) :
    ValueHasType value resultType definitions := by
  obtain ⟨finalStore, steps, _, path⟩ := run_sound result
  have finalTyping := path.preserve_state_type stateTyping
  cases finalTyping with
  | ret storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact valueTyping.erase

theorem closed_well_typed_runStateful_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {expr : Expr} {type : Ty}
    {error : MachineFault} {faultState : State}
    (typing : HasType [] expr type definitions) :
    runStateful fuel (State.initial expr) ≠ .fault error faultState :=
  well_typed_runStateful_never_faults (initial_state_has_type typing)

theorem closed_well_typed_run_stateful_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {expr : Expr} {type : Ty}
    {error : MachineFault} {faultState : State}
    (typing : HasType [] expr type definitions) :
    runStateful fuel (State.initial expr) ≠ .fault error faultState :=
  closed_well_typed_runStateful_never_faults typing

theorem closed_well_typed_run_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {expr : Expr} {type : Ty} {error : MachineFault}
    (typing : HasType [] expr type definitions) :
    run fuel (State.initial expr) ≠ .fault error :=
  well_typed_run_never_faults (initial_state_has_type typing)

theorem Program.checked_runStateful_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value} {finalStore : Store}
    (checked : program.check = true)
    (result : program.runStateful fuel = .done value finalStore) :
    ∃ finalWorld,
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  obtain ⟨world, _, storeTyped, valueTyped⟩ := evaluation_preserves_type
    (runStateful_evaluation_sound result) wellTyped.bodyHasType .nil
      (RuntimeStoreHasTypes.nil program.dataDefinitions)
  exact ⟨world, storeTyped, valueTyped⟩

theorem Program.checked_run_stateful_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value} {finalStore : Store}
    (checked : program.check = true)
    (result : program.runStateful fuel = .done value finalStore) :
    ∃ finalWorld,
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions :=
  Program.checked_runStateful_preserves_result_type checked result

theorem Program.checked_run_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value}
    (checked : program.check = true)
    (result : program.run fuel = .done value) :
    ValueHasType value program.resultType program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  exact well_typed_run_preserves_result_type
    (initial_state_has_type wellTyped.bodyHasType) result

theorem Program.checked_runStateful_completes
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_completes wellTyped.bodyHasType
      evaluation

theorem Program.checked_run_stateful_completes
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions :=
  Program.checked_runStateful_completes checked evaluation

theorem Program.checked_run_completes
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ fuel value,
      program.run fuel = .done value ∧
      ValueHasType value program.resultType program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.run] using
    closed_well_typed_run_completes wellTyped.bodyHasType
      evaluation

theorem Program.checked_runStateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ required finalWorld finalStore value,
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_has_sufficient_fuel
      wellTyped.bodyHasType evaluation

theorem Program.checked_run_stateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ required finalWorld finalStore value,
      RuntimeStoreHasTypes finalWorld finalStore program.dataDefinitions ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore :=
  Program.checked_runStateful_has_sufficient_fuel checked evaluation

theorem Program.checked_run_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] program.body value finalStore) :
    ∃ required value,
      ValueHasType value program.resultType program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.run fuel = .done value := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.run] using
    closed_well_typed_run_has_sufficient_fuel wellTyped.bodyHasType
      evaluation

theorem Program.checked_runStateful_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    {faultState : State}
    (checked : program.check = true) :
    program.runStateful fuel ≠ .fault error faultState := by
  let wellTyped := Program.check_full_sound checked
  exact closed_well_typed_runStateful_never_faults wellTyped.bodyHasType

theorem Program.checked_run_stateful_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    {faultState : State}
    (checked : program.check = true) :
    program.runStateful fuel ≠ .fault error faultState :=
  Program.checked_runStateful_never_faults checked

theorem Program.checked_run_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    (checked : program.check = true) :
    program.run fuel ≠ .fault error := by
  let wellTyped := Program.check_full_sound checked
  exact closed_well_typed_run_never_faults wellTyped.bodyHasType

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.BoundedSafety
/-! Safety of every finite execution, including genuine fuel checkpoints. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Every typed transition retains the current world or allocates a fresh
location at its end. World equality is recovered from the actual shared store. -/
theorem transition_preserves_store_world
    {definitions : DataEnvironment} {state next : State} {type : Ty}
    {world : StoreTyping}
    (typing : StateHasType state type definitions)
    (stored : RuntimeStoreHasTypes world state.store definitions)
    (transition : Transition state next) :
    ∃ future, WorldExtends world future ∧
      RuntimeStoreHasTypes future next.store definitions := by
  cases transition <;> try exact ⟨world, .refl world, stored⟩
  case applyNewCell =>
    cases typing with
    | @ret _ actualWorld _ _ _ _ _ actualStored valueTyped continuationTyped =>
        have same : actualWorld = world :=
          actualStored.world_eq.trans stored.world_eq.symm
        subst actualWorld
        cases continuationTyped with
        | cons frame _ =>
            cases frame with
            | newCellApply =>
                exact ⟨_, ⟨[_], rfl⟩, stored.allocate valueTyped⟩
  case applyStoreCell =>
    rename_i written
    cases typing with
    | @ret _ actualWorld _ _ _ _ _ actualStored valueTyped continuationTyped =>
        have same : actualWorld = world :=
          actualStored.world_eq.trans stored.world_eq.symm
        subst actualWorld
        cases continuationTyped with
        | cons frame _ =>
            cases frame with
            | storeCellApply found =>
                exact ⟨world, .refl world, stored.write found valueTyped written⟩

theorem Steps.preserve_store_world
    {definitions : DataEnvironment} {start finish : State} {type : Ty}
    {world : StoreTyping} {steps : Nat}
    (path : Steps steps start finish)
    (typing : StateHasType start type definitions)
    (stored : RuntimeStoreHasTypes world start.store definitions) :
    ∃ future, WorldExtends world future ∧
      RuntimeStoreHasTypes future finish.store definitions := by
  induction path generalizing world with
  | refl => exact ⟨world, .refl world, stored⟩
  | cons transition tail ih =>
      obtain ⟨middle, extension, middleStored⟩ :=
        transition_preserves_store_world typing stored transition
      obtain ⟨future, further, finalStored⟩ :=
        ih (transition_preserves_state_type typing transition) middleStored
      exact ⟨future, extension.trans further, finalStored⟩

theorem well_typed_runStateful_preserves_checkpoint_world
    {definitions : DataEnvironment} {fuel : Nat} {start checkpoint : State}
    {type : Ty} {world : StoreTyping}
    (typing : StateHasType start type definitions)
    (stored : RuntimeStoreHasTypes world start.store definitions)
    (exhausted : runStateful fuel start = .outOfFuel checkpoint) :
    ∃ future, WorldExtends world future ∧
      RuntimeStoreHasTypes future checkpoint.store definitions :=
  (runStateful_outOfFuel_sound exhausted).1.preserve_store_world typing stored

/-- Completion has a typed value and store; exhaustion retains a typed state.
An internal machine fault is not an admissible typed outcome. -/
def StatefulRunResult.HasType
    (result : StatefulRunResult) (type : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match result with
  | .done value store =>
      ∃ world,
        RuntimeStoreHasTypes world store definitions ∧ RuntimeValueHasType world value type definitions
  | .outOfFuel checkpoint => StateHasType checkpoint type definitions
  | .fault _ _ => False

/-- The actual exhaustion checkpoint has the same result type as the start. -/
theorem well_typed_runStateful_preserves_checkpoint_type
    {definitions : DataEnvironment} {fuel : Nat}
    {start checkpoint : State} {type : Ty}
    (typing : StateHasType start type definitions)
    (exhausted : runStateful fuel start = .outOfFuel checkpoint) :
    StateHasType checkpoint type definitions :=
  (runStateful_outOfFuel_sound exhausted).1.preserve_state_type typing

/-- Finite safety needs no termination assumption or sufficient-fuel bound. -/
theorem well_typed_runStateful_has_type
    {definitions : DataEnvironment} {state : State} {type : Ty}
    (typing : StateHasType state type definitions) (fuel : Nat) :
    (runStateful fuel state).HasType type definitions := by
  cases result : runStateful fuel state with
  | done value store =>
      exact well_typed_runStateful_preserves_result_type typing result
  | outOfFuel checkpoint =>
      exact well_typed_runStateful_preserves_checkpoint_type typing result
  | fault error faultState =>
      exact False.elim (well_typed_runStateful_never_faults typing result)

/-- Resume the retained typed state, preserving the complete outcome invariant. -/
theorem well_typed_runStateful_resume_has_type
    {definitions : DataEnvironment} {spent : Nat}
    {start checkpoint : State} {type : Ty}
    (typing : StateHasType start type definitions)
    (exhausted : runStateful spent start = .outOfFuel checkpoint)
    (additional : Nat) :
    (runStateful additional checkpoint).HasType type definitions ∧
      runStateful additional checkpoint = runStateful (spent + additional) start :=
  ⟨well_typed_runStateful_has_type
      (well_typed_runStateful_preserves_checkpoint_type typing exhausted) additional,
    runStateful_resume exhausted additional⟩

theorem Program.checked_runStateful_has_type
    {program : Program} (checked : program.check = true) (fuel : Nat) :
    (program.runStateful fuel).HasType program.resultType program.dataDefinitions :=
  well_typed_runStateful_has_type
    (initial_state_has_type (Program.check_full_sound checked).bodyHasType) fuel

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.RuntimeStoreSafety
/-! World-indexed store typing and preservation, re-exported from Core safety. -/
end
