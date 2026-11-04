import Solcore.Core.HostTyping
import Solcore.Core.Internal.HostLaws
import Solcore.Core.Safety

/-!
# Preservation and progress with host capabilities

Laws of the relations in `HostTyping`, preservation across Core steps and host requests, and
progress of the host-aware machine. `HostRunner` rests on these.
-/

section
-- leanmerge: from Solcore.Core.HostSafety
/-! Runtime value typing extended additively with fixed host capabilities. -/

set_option autoImplicit false

namespace Solcore.Core

theorem HostRuntimeEnvironmentHasTypes.lookup
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (hasTypes :
      HostRuntimeEnvironmentHasTypes world environment context definitions)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧
        HostRuntimeValueHasType world value type definitions := by
  induction hasTypes using HostRuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | hostFunction | pair | inLeft | inRight | closure
  | cellRef | constructed =>
      exact True.intro
  | nil => simp at typeLookup
  | cons valueTyping _ _ tailIH =>
      cases index with
      | zero =>
          simp at typeLookup
          cases typeLookup
          exact ⟨_, rfl, valueTyping⟩
      | succ index =>
          simp at typeLookup
          obtain ⟨value, valueLookup, valueTyping⟩ := tailIH typeLookup
          exact ⟨value, by simpa using valueLookup, valueTyping⟩

theorem HostRuntimeValueHasType.type_eq
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : HostRuntimeValueHasType world value type definitions) :
    value.type = type := by
  induction typing using HostRuntimeValueHasType.rec
      (motive_2 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | hostFunction | closure | cellRef | constructed => rfl
  | pair _ _ leftIH rightIH => simp [Value.type, leftIH, rightIH]
  | inLeft _ payloadIH => simp [Value.type, payloadIH]
  | inRight _ payloadIH => simp [Value.type, payloadIH]
  | nil | cons => exact True.intro

theorem HostRuntimeValueHasType.word_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value}
    (typing : HostRuntimeValueHasType world value .word definitions) :
    ∃ word, value = .word word := by
  cases typing with
  | word => exact ⟨_, rfl⟩

theorem HostRuntimeValueHasType.unit_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value}
    (typing : HostRuntimeValueHasType world value .unit definitions) :
    value = .unit := by
  cases typing
  rfl

/-- A value typed as a pair of Words has exactly two Word components. -/
theorem HostRuntimeValueHasType.wordPair_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value}
    (typing : HostRuntimeValueHasType world value
      (.product .word .word) definitions) :
    ∃ left right, value = .pair (.word left) (.word right) := by
  cases typing with
  | pair leftTyping rightTyping =>
      obtain ⟨left, rfl⟩ := leftTyping.word_shape
      obtain ⟨right, rfl⟩ := rightTyping.word_shape
      exact ⟨left, right, rfl⟩

/-- A value typed as a target/value/input tuple has exactly three Word leaves. -/
theorem HostRuntimeValueHasType.wordTriple_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value}
    (typing : HostRuntimeValueHasType world value
      (.product .word (.product .word .word)) definitions) :
    ∃ first second third,
      value = .pair (.word first) (.pair (.word second) (.word third)) := by
  cases typing with
  | pair firstTyping restTyping =>
      obtain ⟨first, rfl⟩ := firstTyping.word_shape
      obtain ⟨second, third, rfl⟩ := restTyping.wordPair_shape
      exact ⟨first, second, third, rfl⟩

theorem HostRuntimeValueHasType.function_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value} {parameterType resultType : Ty}
    (typing : HostRuntimeValueHasType world value
      (.function parameterType resultType) definitions) :
    (∃ body environment,
      value = .closure parameterType resultType body environment) ∨
    (∃ function,
      value = .hostFunction function ∧
        function.functionType = .function parameterType resultType) := by
  cases typing with
  | hostFunction => exact .inr ⟨_, rfl, rfl⟩
  | closure => exact .inl ⟨_, _, rfl⟩

/-- Any ordered list of host capabilities is typed by its mapped type list. -/
theorem hostFunctions_haveTypes
    (world : StoreTyping)
    (functions : List HostFunction)
    (definitions : DataEnvironment := []) :
    HostRuntimeEnvironmentHasTypes world
      (functions.map fun function => .hostFunction function)
      (functions.map HostFunction.functionType)
      definitions := by
  induction functions with
  | nil => exact .nil
  | cons function functions ih =>
      exact .cons .hostFunction ih

@[simp] theorem hostEnvironment_hasTypes
    (world : StoreTyping)
    (definitions : DataEnvironment := []) :
  HostRuntimeEnvironmentHasTypes world hostEnvironment hostContext definitions := by
  simpa only [hostEnvironment, hostContext] using
    hostFunctions_haveTypes world HostFunction.all definitions

mutual

  theorem RuntimeValueHasType.toHost
      {definitions : DataEnvironment}
      {world : StoreTyping} {value : Value} {type : Ty}
      (typing : RuntimeValueHasType world value type definitions) :
      HostRuntimeValueHasType world value type definitions := by
    induction typing using RuntimeValueHasType.rec with
    | unit => exact .unit
    | bool => exact .bool
    | word => exact .word
    | integer => exact .integer
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | inLeft _ payloadIH => exact .inLeft payloadIH
    | inRight _ payloadIH => exact .inRight payloadIH
    | closure _ bodyTyping environmentIH =>
        exact .closure environmentIH bodyTyping
    | cellRef found => exact .cellRef found
    | constructed lookup _ payloadIH => exact .constructed lookup payloadIH
    | nil => exact .nil
    | cons _ _ valueIH environmentIH => exact .cons valueIH environmentIH

  theorem RuntimeEnvironmentHasTypes.toHost
      {definitions : DataEnvironment}
      {world : StoreTyping} {environment : Environment} {context : Context}
      (typing : RuntimeEnvironmentHasTypes world environment context definitions) :
      HostRuntimeEnvironmentHasTypes world environment context definitions := by
    apply RuntimeEnvironmentHasTypes.rec
        (world := world)
        (motive_1 := fun value type relationDefinitions _ =>
          HostRuntimeValueHasType world value type relationDefinitions)
        (motive_2 := fun relationEnvironment relationContext
            relationDefinitions _ =>
          HostRuntimeEnvironmentHasTypes world relationEnvironment
            relationContext relationDefinitions)
        (t := typing)
    case unit => intros; exact .unit
    case bool => intros; exact .bool
    case word => intros; exact .word
    case integer => intros; exact .integer
    case pair =>
      intro _ _ _ _ _ _ _ leftIH rightIH
      exact .pair leftIH rightIH
    case inLeft =>
      intro _ _ _ _ _ payloadIH
      exact .inLeft payloadIH
    case inRight =>
      intro _ _ _ _ _ payloadIH
      exact .inRight payloadIH
    case closure =>
      intro _ _ _ _ _ _ _ bodyTyping environmentIH
      exact .closure environmentIH bodyTyping
    case cellRef =>
      intro _ _ _ found
      exact .cellRef found
    case constructed =>
      intro _ _ _ _ lookup _ payloadIH
      exact .constructed lookup payloadIH
    case nil => intros; exact .nil
    case cons =>
      intro _ _ _ _ _ _ _ valueIH environmentIH
      exact .cons valueIH environmentIH

end

theorem HostRuntimeValueHasType.weaken
    {definitions : DataEnvironment} {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {value : Value} {type : Ty}
    (typing : HostRuntimeValueHasType initial value type definitions) :
    HostRuntimeValueHasType future value type definitions := by
  apply HostRuntimeValueHasType.rec
      (world := initial)
      (motive_1 := fun value type relationDefinitions _ =>
        HostRuntimeValueHasType future value type relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        HostRuntimeEnvironmentHasTypes future environment context
          relationDefinitions)
      (t := typing)
  case unit => intros; exact .unit
  case bool => intros; exact .bool
  case word => intros; exact .word
  case integer => intros; exact .integer
  case hostFunction => intros; exact .hostFunction
  case pair => intros; exact .pair ‹_› ‹_›
  case inLeft => intros; exact .inLeft ‹_›
  case inRight => intros; exact .inRight ‹_›
  case closure => intros; exact .closure ‹_› ‹_›
  case cellRef => intros; exact .cellRef (extension.lookup ‹_›)
  case constructed => intros; exact .constructed ‹_› ‹_›
  case nil => intros; exact .nil
  case cons => intros; exact .cons ‹_› ‹_›

theorem HostRuntimeEnvironmentHasTypes.weaken
    {definitions : DataEnvironment} {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {environment : Environment} {context : Context}
    (typing : HostRuntimeEnvironmentHasTypes initial environment context definitions) :
    HostRuntimeEnvironmentHasTypes future environment context definitions := by
  induction typing using HostRuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | hostFunction | pair | inLeft | inRight | closure
  | cellRef | constructed =>
      exact True.intro
  | nil => exact .nil
  | cons valueTyping _ _ environmentIH =>
      exact .cons (valueTyping.weaken extension) environmentIH

/-- First-order cell payloads contain no host capabilities. -/
theorem CellPayload.valueHasType_of_hostRuntimeValueHasType
    {elementType : Ty}
    (payload : CellPayload elementType)
    {definitions : DataEnvironment} {world : StoreTyping} {value : Value}
    (typing : HostRuntimeValueHasType world value elementType definitions) :
    ValueHasType value elementType definitions := by
  induction payload generalizing value with
  | unit => cases typing; exact .unit
  | bool => cases typing; exact .bool
  | word => cases typing; exact .word
  | integer => cases typing; exact .integer
  | product leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          exact .pair (leftIH leftTyping) (rightIH rightTyping)
  | sum leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | inLeft payloadTyping => exact .inLeft (leftIH payloadTyping)
      | inRight payloadTyping => exact .inRight (rightIH payloadTyping)

namespace HostStoreHasTypes

theorem nil {definitions : DataEnvironment} :
    HostStoreHasTypes [] [] definitions where
  length_eq := rfl
  lookup := by simp

theorem read
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : HostStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    ∃ value,
      store.read? location = some value ∧
      HostRuntimeValueHasType world value elementType definitions :=
  typing.lookup found

theorem location_lt
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : HostStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    location < store.length := by
  have worldBound : location < world.length :=
    (List.getElem?_eq_some_iff.mp found).1
  simpa [← typing.length_eq] using worldBound

theorem allocate
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : HostStoreHasTypes world store definitions)
    {elementType : Ty} {value : Value}
    (valueTyping : HostRuntimeValueHasType world value elementType definitions) :
    HostStoreHasTypes (world ++ [elementType])
      (store.allocate value).1 definitions := by
  have extension : WorldExtends world (world ++ [elementType]) :=
    ⟨[elementType], rfl⟩
  constructor
  · simp [typing.length_eq]
  · intro location storedType foundType
    by_cases old : location < world.length
    · have oldType : world[location]? = some storedType := by
        rw [List.getElem?_append_left (l₂ := [elementType]) old] at foundType
        exact foundType
      obtain ⟨oldValue, oldLookup, oldTyping⟩ := typing.lookup oldType
      have storeOld : location < store.length := by
        simpa [← typing.length_eq] using old
      exact ⟨oldValue,
        (Store.allocate_old_lookup store value storeOld).trans oldLookup,
        oldTyping.weaken extension⟩
    · have locationEq : location = world.length := by
        have bound : location < (world ++ [elementType]).length :=
          (List.getElem?_eq_some_iff.mp foundType).1
        have upper : location ≤ world.length := by
          apply Nat.lt_succ_iff.mp
          simpa using bound
        exact Nat.le_antisymm upper (Nat.le_of_not_gt old)
      subst location
      have storedTypeEq : storedType = elementType := by
        have equality : some elementType = some storedType := by
          simpa using foundType
        exact (Option.some.inj equality).symm
      subst storedType
      exact ⟨value,
        by simpa [← typing.length_eq] using
          Store.allocate_fresh_lookup store value,
        valueTyping.weaken extension⟩

theorem write
    {definitions : DataEnvironment}
    {world : StoreTyping} {store updatedStore : Store}
    (typing : HostStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType)
    (valueTyping : HostRuntimeValueHasType world value elementType definitions)
    (written : store.write? location value = some updatedStore) :
    HostStoreHasTypes world updatedStore definitions := by
  constructor
  · rw [Store.write?_preserves_length written]
    exact typing.length_eq
  · intro otherLocation otherType otherFound
    obtain ⟨oldValue, oldLookup, oldTyping⟩ := typing.lookup otherFound
    by_cases same : otherLocation = location
    · subst otherLocation
      have typeEq : elementType = otherType :=
        Option.some.inj (found.symm.trans otherFound)
      subst typeEq
      exact ⟨value, Store.write?_reads_written written, valueTyping⟩
    · exact ⟨oldValue,
        (Store.write?_preserves_other written same).trans oldLookup,
        oldTyping⟩

theorem write_exists
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : HostStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType) :
    ∃ updatedStore, store.write? location value = some updatedStore :=
  (Store.write?_success_iff store location value).2 (typing.location_lt found)

end HostStoreHasTypes

/-- Higher-order pure stores embed in the host machine with the same world. -/
theorem RuntimeStoreHasTypes.toHost
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions) :
    HostStoreHasTypes world store definitions where
  length_eq := typing.length_eq
  lookup := by
    intro location elementType found
    obtain ⟨value, lookup, valueTyping⟩ := typing.lookup found
    exact ⟨value, lookup, valueTyping.toHost⟩

/-- Pure stores can be used by the host machine without adding capabilities. -/
theorem StoreHasTypes.toHost
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store) :
    HostStoreHasTypes world store definitions where
  length_eq := typing.length_eq
  lookup := by
    intro location elementType found
    obtain ⟨value, lookup, payload, valueTyping⟩ := typing.lookup found
    exact ⟨value, lookup, (payload.runtimeValueHasType valueTyping definitions).toHost⟩

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.HostStateSafety
/-! Typing for CEK states that may carry fixed host capabilities. -/

set_option autoImplicit false

namespace Solcore.Core

theorem HostFrameHasType.weaken {definitions : DataEnvironment}
    {initial future : StoreTyping} (extension : WorldExtends initial future)
    {frame : Frame} {inputType outputType : Ty}
    (typing : HostFrameHasType initial frame inputType outputType definitions) :
    HostFrameHasType future frame inputType outputType definitions := by
  cases typing with
  | unaryApply => exact .unaryApply
  | binaryRight env expr => exact .binaryRight (env.weaken extension) expr
  | binaryApply value => exact .binaryApply (value.weaken extension)
  | ternarySecond env second third => exact .ternarySecond (env.weaken extension) second third
  | ternaryThird first env third => exact .ternaryThird (first.weaken extension) (env.weaken extension) third
  | ternaryApply first second => exact .ternaryApply (first.weaken extension) (second.weaken extension)
  | pairRight env right => exact .pairRight (env.weaken extension) right
  | pairApply left => exact .pairApply (left.weaken extension)
  | firstApply => exact .firstApply
  | secondApply => exact .secondApply
  | inLeftApply => exact .inLeftApply
  | inRightApply => exact .inRightApply
  | caseBranches env left right => exact .caseBranches (env.weaken extension) left right
  | newCellApply => exact .newCellApply
  | loadCellApply => exact .loadCellApply
  | storeCellValue env value => exact .storeCellValue (env.weaken extension) value
  | storeCellApply found => exact .storeCellApply (extension.lookup found)
  | constructApply lookup => exact .constructApply lookup
  | matchDataApply lookup env branches => exact .matchDataApply lookup (env.weaken extension) branches
  | applyArgument env argument => exact .applyArgument (env.weaken extension) argument
  | applyClosure env body => exact .applyClosure (env.weaken extension) body
  | hostApply => exact .hostApply
  | letBody env body => exact .letBody (env.weaken extension) body
  | ifBranches env thenType elseType => exact .ifBranches (env.weaken extension) thenType elseType

theorem HostContinuationHasType.weaken {definitions : DataEnvironment}
    {initial future : StoreTyping} (extension : WorldExtends initial future)
    {continuation : List Frame} {inputType outputType : Ty}
    (typing : HostContinuationHasType initial continuation inputType outputType definitions) :
    HostContinuationHasType future continuation inputType outputType definitions := by
  induction typing with
  | nil => exact .nil
  | cons frame _ tail => exact .cons (frame.weaken extension) tail

theorem HostRequest.responseValue_hasType
    (request : HostRequest) (response : request.Response)
    (world : StoreTyping) (definitions : DataEnvironment := []) :
    HostRuntimeValueHasType world (request.responseValue response)
      request.responseType definitions := by
  cases request with
  | storageRead => exact .word
  | storageWrite => exact .unit
  | storageAddress => exact .word
  | codeAddress => exact .word
  | callValue => exact .word
  | callerAddress => exact .word
  | inputDataByte? =>
      cases response with
      | none => exact .inLeft .unit
      | some => exact .inRight .word
  | inputDataSize => exact .word
  | inputDataWordBE? =>
      cases response with
      | none => exact .inLeft .unit
      | some => exact .inRight .word
  | currentAddress => exact .word
  | callContractWord =>
      cases response with
      | returned => exact .inLeft .word
      | reverted => exact .inRight (.inLeft .word)
      | trapped => exact .inRight (.inRight (.inLeft .word))
      | failed => exact .inRight (.inRight (.inRight .word))
  | callContractWordWithValue =>
      cases response with
      | returned => exact .inLeft .word
      | reverted => exact .inRight (.inLeft .word)
      | trapped => exact .inRight (.inRight (.inLeft .word))
      | failed => exact .inRight (.inRight (.inRight .word))
  | createContractWord =>
      cases response with
      | returned => exact .inLeft .word
      | reverted => exact .inRight (.inLeft .word)
      | trapped => exact .inRight (.inRight (.inLeft .word))
      | failed => exact .inRight (.inRight (.inRight .word))
  | emitLogWord => exact .unit

theorem HostSuspensionHasType.resume {definitions : DataEnvironment}
    {suspension : HostSuspension} {resultType : Ty}
    (typing : HostSuspensionHasType suspension resultType definitions)
    (response : suspension.request.Response) :
    HostStateHasType (suspension.resume response) resultType definitions := by
  cases typing with
  | intro storeTyping continuationTyping =>
      exact .ret storeTyping
        (HostRequest.responseValue_hasType _ response _ definitions)
        continuationTyping

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.ContractCallWordResultProperties
/-! Exact decoding and injectivity for the typed contract-word call response. -/

set_option autoImplicit false

namespace Solcore.Core.ContractCallWordResult

/-- Recognize only the four canonical values emitted by `value`. -/
def ofValue? : Value → Option ContractCallWordResult
  | .inLeft (.sum .word (.sum .word .word)) (.word data) =>
      some (.returned data)
  | .inRight .word
      (.inLeft (.sum .word .word) (.word data)) =>
      some (.reverted data)
  | .inRight .word
      (.inRight .word (.inLeft .word (.word reason))) =>
      some (.trapped reason)
  | .inRight .word
      (.inRight .word (.inRight .word (.word reason))) =>
      some (.failed reason)
  | _ => none

@[simp] theorem ofValue?_value (result : ContractCallWordResult) :
    ofValue? result.value = some result := by
  cases result <;> rfl

/-- The four response constructors have disjoint, payload-preserving encodings. -/
theorem value_injective : Function.Injective value := by
  intro left right equality
  have decoded := congrArg ofValue? equality
  simpa using decoded

theorem value_eq_iff (left right : ContractCallWordResult) :
    left.value = right.value ↔ left = right :=
  ⟨fun equal => value_injective equal, congrArg value⟩

end Solcore.Core.ContractCallWordResult
end

section
-- leanmerge: from Solcore.Core.HostCoreTransitionSafety
/-! Preservation of host-aware state typing by ordinary Core transitions. -/

set_option autoImplicit false

namespace Solcore.Core

theorem transition_preserves_host_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (transition : Transition state next) :
    HostStateHasType next resultType definitions := by
  cases transition with
  | unit =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .unit cont
  | bool =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .bool cont
  | word =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .word cont
  | integer =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .integer cont
  | enterPair =>
      cases stateTyping with
      | eval store env expr cont =>
          cases expr with
          | pair left right => exact .eval store env left (.cons (.pairRight env right) cont)
  | enterPairRight =>
      cases stateTyping with
      | ret store left cont =>
          cases cont with
          | cons frame rest => cases frame with
            | pairRight env right => exact .eval store env right (.cons (.pairApply left) rest)
  | applyPair =>
      cases stateTyping with
      | ret store right cont => cases cont with
        | cons frame rest => cases frame with
          | pairApply left => exact .ret store (.pair left right) rest
  | enterFirst =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | first operand => exact .eval store env operand (.cons .firstApply cont)
  | applyFirst =>
      cases stateTyping with
      | ret store pair cont => cases cont with
        | cons frame rest => cases frame with
          | firstApply => cases pair with
            | pair left _ => exact .ret store left rest
  | enterSecond =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | second operand => exact .eval store env operand (.cons .secondApply cont)
  | applySecond =>
      cases stateTyping with
      | ret store pair cont => cases cont with
        | cons frame rest => cases frame with
          | secondApply => cases pair with
            | pair _ right => exact .ret store right rest
  | enterInLeft =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | inLeft _ payload => exact .eval store env payload (.cons .inLeftApply cont)
  | applyInLeft =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | inLeftApply => exact .ret store (.inLeft payload) rest
  | enterInRight =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | inRight _ payload => exact .eval store env payload (.cons .inRightApply cont)
  | applyInRight =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | inRightApply => exact .ret store (.inRight payload) rest
  | enterCase =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | caseE scrutinee left right =>
            exact .eval store env scrutinee (.cons (.caseBranches env left right) cont)
  | chooseLeft =>
      cases stateTyping with
      | ret store sum cont => cases cont with
        | cons frame rest => cases frame with
          | caseBranches env left right => cases sum with
            | inLeft payload => exact .eval store (.cons payload env) left rest
  | chooseRight =>
      cases stateTyping with
      | ret store sum cont => cases cont with
        | cons frame rest => cases frame with
          | caseBranches env left right => cases sum with
            | inRight payload => exact .eval store (.cons payload env) right rest
  | enterNewCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | newCell initializer =>
            exact .eval store env initializer (.cons .newCellApply cont)
  | @applyNewCell elementType initialValue continuation store =>
      cases stateTyping with
      | @ret _ world _ _ _ _ _ storeTyping valueTyping cont => cases cont with
        | cons frame rest => cases frame with
          | newCellApply =>
              let futureWorld := world ++ [elementType]
              have extension : WorldExtends world futureWorld := ⟨[elementType], rfl⟩
              have futureStore : HostStoreHasTypes futureWorld (store.allocate initialValue).1 definitions := by
                simpa [futureWorld] using storeTyping.allocate valueTyping
              have fresh : futureWorld[(store.allocate initialValue).2]? = some elementType := by
                simp [futureWorld, Store.allocate, ← storeTyping.length_eq]
              exact .ret futureStore (.cellRef fresh) (rest.weaken extension)
  | enterLoadCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | loadCell reference =>
            exact .eval store env reference (.cons .loadCellApply cont)
  | applyLoadCell loaded =>
      cases stateTyping with
      | ret store cell cont => cases cont with
        | cons frame rest => cases frame with
          | loadCellApply => cases cell with
            | cellRef found =>
                obtain ⟨stored, read, typing⟩ := store.lookup found
                rw [loaded] at read
                cases read
                exact .ret store typing rest
  | enterStoreCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | storeCell reference value =>
            exact .eval store env reference (.cons (.storeCellValue env value) cont)
  | beginStoreCellValue _ =>
      cases stateTyping with
      | ret store cell cont => cases cont with
        | cons frame rest => cases frame with
          | storeCellValue env value => cases cell with
            | cellRef found => exact .eval store env value (.cons (.storeCellApply found) rest)
  | applyStoreCell written =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | storeCellApply found =>
              exact .ret (store.write found value written) .unit rest
  | enterConstruct =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | construct lookup payload => exact .eval store env payload (.cons (.constructApply lookup) cont)
  | applyConstruct =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | constructApply lookup => exact .ret store (.constructed lookup payload) rest
  | enterMatchData =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | matchData lookup _ scrutinee branches =>
            exact .eval store env scrutinee (.cons (.matchDataApply lookup env branches) cont)
  | chooseData ownerEq branchLookup =>
      cases stateTyping with
      | ret store data cont => cases cont with
        | cons frame rest => cases frame with
          | matchDataApply definitionLookup env branches => cases data with
            | constructed constructorLookup payload =>
                obtain ⟨_, runtimeLookup, payloadLookup⟩ :=
                  DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp constructorLookup
                rw [ownerEq] at runtimeLookup
                have typedLookup := DataEnvironment.lookupDataType?_eq_some_iff.mp definitionLookup
                rw [typedLookup] at runtimeLookup
                cases runtimeLookup
                exact .eval store (.cons payload env)
                  (branches.lookup payloadLookup branchLookup) rest
  | lambda =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | lambda _ _ body => exact .ret store (.closure env body) cont
  | enterApply =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | apply function argument =>
            exact .eval store env function (.cons (.applyArgument env argument) cont)
  | beginArgument =>
      cases stateTyping with
      | ret store function cont => cases cont with
        | cons frame rest => cases frame with
          | applyArgument caller argument => cases function with
            | closure captured body =>
                exact .eval store caller argument (.cons (.applyClosure captured body) rest)
  | invokeClosure =>
      cases stateTyping with
      | ret store argument cont => cases cont with
        | cons frame rest => cases frame with
          | applyClosure captured body =>
              exact .eval store (.cons argument captured) body rest
  | var valueLookup =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | var typeLookup =>
            obtain ⟨found, foundLookup, foundTyping⟩ := env.lookup typeLookup
            rw [valueLookup] at foundLookup
            cases foundLookup
            exact .ret store foundTyping cont
  | enterUnary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | unary operand => exact .eval store env operand (.cons .unaryApply cont)
  | applyUnary applied =>
      cases stateTyping with
      | ret store operand cont => cases cont with
        | cons frame rest => cases frame with
          | unaryApply =>
              exact .ret store (RuntimeValueHasType.toHost
                (unary_apply_result_has_runtime_type applied definitions)) rest
  | enterBinary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | binary left right => exact .eval store env left (.cons (.binaryRight env right) cont)
  | enterBinaryRight =>
      cases stateTyping with
      | ret store left cont => cases cont with
        | cons frame rest => cases frame with
          | binaryRight env right => exact .eval store env right (.cons (.binaryApply left) rest)
  | applyBinary applied =>
      cases stateTyping with
      | ret store right cont => cases cont with
        | cons frame rest => cases frame with
          | binaryApply left =>
              exact .ret store (RuntimeValueHasType.toHost
                (binary_apply_result_has_runtime_type applied definitions)) rest
  | enterTernary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | ternary first second third =>
            exact .eval store env first (.cons (.ternarySecond env second third) cont)
  | enterTernarySecond =>
      cases stateTyping with
      | ret store first cont => cases cont with
        | cons frame rest => cases frame with
          | ternarySecond env second third =>
              exact .eval store env second (.cons (.ternaryThird first env third) rest)
  | enterTernaryThird =>
      cases stateTyping with
      | ret store second cont => cases cont with
        | cons frame rest => cases frame with
          | ternaryThird first env third =>
              exact .eval store env third (.cons (.ternaryApply first second) rest)
  | applyTernary applied =>
      cases stateTyping with
      | ret store third cont => cases cont with
        | cons frame rest => cases frame with
          | ternaryApply first second =>
              exact .ret store (RuntimeValueHasType.toHost
                (ternary_apply_result_has_runtime_type applied definitions)) rest
  | enterLet =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | letE bound body => exact .eval store env bound (.cons (.letBody env body) cont)
  | bindLet =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | letBody env body => exact .eval store (.cons value env) body rest
  | enterIf =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | ifE condition thenType elseType =>
            exact .eval store env condition (.cons (.ifBranches env thenType elseType) cont)
  | chooseTrue =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | ifBranches env thenType elseType => exact .eval store env thenType rest
  | chooseFalse =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | ifBranches env thenType elseType => exact .eval store env elseType rest

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.HostTransitionSafety
/-! Type preservation at the executable Core/host boundary. -/

set_option autoImplicit false

namespace Solcore.Core

theorem hostTransition_preserves_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (transition : HostTransition state next) :
    HostStateHasType next resultType definitions := by
  cases transition with
  | core step =>
      exact transition_preserves_host_state_type stateTyping step
  | beginApplication =>
      cases stateTyping with
      | ret store functionTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyArgument environmentTyping argumentTyping =>
                  cases functionTyping with
                  | hostFunction =>
                      exact .eval store environmentTyping argumentTyping
                        (.cons .hostApply restTyping)

theorem hostRequestEmission_hasType
    {definitions : DataEnvironment}
    {state : State} {suspension : HostSuspension} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (emission : HostRequestEmission state suspension) :
    HostSuspensionHasType suspension resultType definitions := by
  cases emission with
  | storageRead =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | word => exact .intro store restTyping
  | storageWrite =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair leftTyping rightTyping =>
                      cases leftTyping
                      cases rightTyping
                      exact .intro store restTyping
  | storageAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | codeAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | callValue =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | callerAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | inputDataByte? =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | word => exact .intro store restTyping
  | inputDataSize =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | inputDataWordBE? =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | word => exact .intro store restTyping
  | currentAddress =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping
                  exact .intro store restTyping
  | callContractWord =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair leftTyping rightTyping =>
                      cases leftTyping
                      cases rightTyping
                      exact .intro store restTyping
  | callContractWordWithValue =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair targetTyping restTyping' =>
                      cases targetTyping
                      cases restTyping' with
                      | pair valueTyping inputTyping =>
                          cases valueTyping
                          cases inputTyping
                          exact .intro store restTyping
  | createContractWord =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair templateTyping restTyping' =>
                      cases templateTyping
                      cases restTyping' with
                      | pair valueTyping inputTyping =>
                          cases valueTyping
                          cases inputTyping
                          exact .intro store restTyping
  | emitLogWord =>
      cases stateTyping with
      | ret store valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | hostApply =>
                  cases valueTyping with
                  | pair topicTyping payloadTyping =>
                      cases topicTyping
                      cases payloadTyping
                      exact .intro store restTyping

theorem hostAdvance_next_preserves_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (advanced : hostAdvance state = .next next) :
    HostStateHasType next resultType definitions :=
  hostTransition_preserves_state_type stateTyping (hostAdvance_next_iff.mp advanced)

theorem hostAdvance_suspended_hasType
    {definitions : DataEnvironment}
    {state : State} {suspension : HostSuspension} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (advanced : hostAdvance state = .suspended suspension) :
    HostSuspensionHasType suspension resultType definitions :=
  hostRequestEmission_hasType stateTyping (hostAdvance_suspended_iff.mp advanced)

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.HostProgress
/-! Progress and immediate fault freedom for the host-aware CEK machine. -/

set_option autoImplicit false

namespace Solcore.Core

/-- A well-typed storage-read argument emits the corresponding request. -/
theorem typed_storageRead_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageRead.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageRead :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨slot, rfl⟩ := wordTyping.word_shape
  exact ⟨⟨.storageRead slot, continuation, store⟩, .storageRead⟩

/-- A well-typed storage-write argument emits the corresponding request. -/
theorem typed_storageWrite_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageWrite.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageWrite :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨slot, writtenValue, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.storageWrite slot writtenValue, continuation, store⟩,
      .storageWrite⟩

/-- A well-typed storage-address observation emits its argument-free request. -/
theorem typed_storageAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.storageAddress, continuation, store⟩, .storageAddress⟩

/-- A well-typed code-address observation emits its argument-free request. -/
theorem typed_codeAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.codeAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .codeAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.codeAddress, continuation, store⟩, .codeAddress⟩

/-- A well-typed call-value observation emits its argument-free request. -/
theorem typed_callValue_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callValue.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callValue :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.callValue, continuation, store⟩, .callValue⟩

/-- A well-typed caller-address observation emits its argument-free request. -/
theorem typed_callerAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callerAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callerAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.callerAddress, continuation, store⟩, .callerAddress⟩

/-- A well-typed input-data byte offset emits its optional read request. -/
theorem typed_inputDataByte?_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataByte?.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataByte? :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨offset, rfl⟩ := wordTyping.word_shape
  exact ⟨⟨.inputDataByte? offset, continuation, store⟩, .inputDataByte?⟩

/-- A well-typed input-size observation emits its argument-free request. -/
theorem typed_inputDataSize_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataSize.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataSize :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.inputDataSize, continuation, store⟩, .inputDataSize⟩

/-- A well-typed input-data word offset emits its optional read request. -/
theorem typed_inputDataWordBE?_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataWordBE?.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataWordBE? :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨offset, rfl⟩ := wordTyping.word_shape
  exact
    ⟨⟨.inputDataWordBE? offset, continuation, store⟩,
      .inputDataWordBE?⟩

/-- A well-typed current-address observation emits its argument-free request. -/
theorem typed_currentAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.currentAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .currentAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.currentAddress, continuation, store⟩, .currentAddress⟩

/-- A well-typed target/input pair emits one contract-word call request. -/
theorem typed_callContractWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callContractWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callContractWord :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨target, input, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.callContractWord target input, continuation, store⟩,
      .callContractWord⟩

/-- A well-typed target/value/input tuple emits one value-bearing call. -/
theorem typed_callContractWordWithValue_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callContractWordWithValue.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value,
          .hostApply .callContractWordWithValue :: continuation, store⟩
        suspension := by
  have tupleTyping :
      HostRuntimeValueHasType world value
        (.product .word (.product .word .word)) definitions := by
    simpa using valueTyping
  obtain ⟨target, transferredValue, input, rfl⟩ :=
    tupleTyping.wordTriple_shape
  exact
    ⟨⟨.callContractWordWithValue target transferredValue input,
        continuation, store⟩,
      .callContractWordWithValue⟩

/-- A well-typed template/value/input tuple emits one creation request. -/
theorem typed_createContractWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.createContractWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value,
          .hostApply .createContractWord :: continuation, store⟩
        suspension := by
  have tupleTyping :
      HostRuntimeValueHasType world value
        (.product .word (.product .word .word)) definitions := by
    simpa using valueTyping
  obtain ⟨templateId, transferredValue, input, rfl⟩ :=
    tupleTyping.wordTriple_shape
  exact
    ⟨⟨.createContractWord templateId transferredValue input,
        continuation, store⟩,
      .createContractWord⟩

/-- A well-typed topic/payload pair emits one log request. -/
theorem typed_emitLogWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.emitLogWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .emitLogWord :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨topic, payload, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.emitLogWord topic payload, continuation, store⟩,
      .emitLogWord⟩

/-- Capability dispatch is kept separate from the general CEK progress proof. -/
theorem typed_hostApplication_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {function : HostFunction} {value : Value}
    {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      function.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply function :: continuation, store⟩
        suspension := by
  cases function with
  | storageRead => exact typed_storageRead_emits valueTyping
  | storageWrite => exact typed_storageWrite_emits valueTyping
  | storageAddress => exact typed_storageAddress_emits valueTyping
  | codeAddress => exact typed_codeAddress_emits valueTyping
  | callValue => exact typed_callValue_emits valueTyping
  | callerAddress => exact typed_callerAddress_emits valueTyping
  | inputDataByte? => exact typed_inputDataByte?_emits valueTyping
  | inputDataSize => exact typed_inputDataSize_emits valueTyping
  | inputDataWordBE? => exact typed_inputDataWordBE?_emits valueTyping
  | currentAddress => exact typed_currentAddress_emits valueTyping
  | callContractWord => exact typed_callContractWord_emits valueTyping
  | callContractWordWithValue =>
      exact typed_callContractWordWithValue_emits valueTyping
  | createContractWord =>
      exact typed_createContractWord_emits valueTyping
  | emitLogWord =>
      exact typed_emitLogWord_emits valueTyping

theorem host_state_progress
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions) :
    (∃ value store, state = State.final value store) ∨
      (∃ next, HostTransition state next) ∨
      ∃ suspension, HostRequestEmission state suspension := by
  cases stateTyping with
  | eval storeTyping environmentTyping exprTyping continuationTyping =>
      cases exprTyping with
      | unit => exact .inr (.inl ⟨_, .core .unit⟩)
      | bool => exact .inr (.inl ⟨_, .core .bool⟩)
      | word => exact .inr (.inl ⟨_, .core .word⟩)
      | integer => exact .inr (.inl ⟨_, .core .integer⟩)
      | var typeLookup =>
          obtain ⟨value, valueLookup, _⟩ := environmentTyping.lookup typeLookup
          exact .inr (.inl ⟨_, .core (.var valueLookup)⟩)
      | pair => exact .inr (.inl ⟨_, .core .enterPair⟩)
      | first => exact .inr (.inl ⟨_, .core .enterFirst⟩)
      | second => exact .inr (.inl ⟨_, .core .enterSecond⟩)
      | lambda => exact .inr (.inl ⟨_, .core .lambda⟩)
      | apply => exact .inr (.inl ⟨_, .core .enterApply⟩)
      | inLeft => exact .inr (.inl ⟨_, .core .enterInLeft⟩)
      | inRight => exact .inr (.inl ⟨_, .core .enterInRight⟩)
      | caseE => exact .inr (.inl ⟨_, .core .enterCase⟩)
      | newCell => exact .inr (.inl ⟨_, .core .enterNewCell⟩)
      | loadCell => exact .inr (.inl ⟨_, .core .enterLoadCell⟩)
      | storeCell => exact .inr (.inl ⟨_, .core .enterStoreCell⟩)
      | construct => exact .inr (.inl ⟨_, .core .enterConstruct⟩)
      | matchData => exact .inr (.inl ⟨_, .core .enterMatchData⟩)
      | unary => exact .inr (.inl ⟨_, .core .enterUnary⟩)
      | binary => exact .inr (.inl ⟨_, .core .enterBinary⟩)
      | ternary => exact .inr (.inl ⟨_, .core .enterTernary⟩)
      | letE => exact .inr (.inl ⟨_, .core .enterLet⟩)
      | ifE => exact .inr (.inl ⟨_, .core .enterIf⟩)
  | @ret _ world value continuation store controlType resultType
      storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact .inl ⟨value, store, rfl⟩
      | cons frameTyping restTyping =>
          cases frameTyping with
          | unaryApply =>
              obtain ⟨result, applied, _⟩ :=
                UnaryOp.apply_total_of_type _ _ valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyUnary applied)⟩)
          | binaryRight => exact .inr (.inl ⟨_, .core .enterBinaryRight⟩)
          | binaryApply leftTyping =>
              obtain ⟨result, applied, _⟩ :=
                BinaryOp.apply_total_of_types _ _ _
                  leftTyping.type_eq valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyBinary applied)⟩)
          | ternarySecond =>
              exact .inr (.inl ⟨_, .core .enterTernarySecond⟩)
          | ternaryThird => exact .inr (.inl ⟨_, .core .enterTernaryThird⟩)
          | ternaryApply firstTyping secondTyping =>
              obtain ⟨result, applied, _⟩ :=
                TernaryOp.apply_total_of_types _ _ _ _
                  firstTyping.type_eq secondTyping.type_eq valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyTernary applied)⟩)
          | pairRight => exact .inr (.inl ⟨_, .core .enterPairRight⟩)
          | pairApply => exact .inr (.inl ⟨_, .core .applyPair⟩)
          | firstApply =>
              cases valueTyping with
              | pair => exact .inr (.inl ⟨_, .core .applyFirst⟩)
          | secondApply =>
              cases valueTyping with
              | pair => exact .inr (.inl ⟨_, .core .applySecond⟩)
          | inLeftApply => exact .inr (.inl ⟨_, .core .applyInLeft⟩)
          | inRightApply => exact .inr (.inl ⟨_, .core .applyInRight⟩)
          | caseBranches =>
              cases valueTyping with
              | inLeft => exact .inr (.inl ⟨_, .core .chooseLeft⟩)
              | inRight => exact .inr (.inl ⟨_, .core .chooseRight⟩)
          | newCellApply => exact .inr (.inl ⟨_, .core .applyNewCell⟩)
          | loadCellApply =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨loaded, read, _⟩ := storeTyping.lookup found
                  exact .inr (.inl ⟨_, .core (.applyLoadCell read)⟩)
          | storeCellValue _ _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨oldValue, read, _⟩ := storeTyping.lookup found
                  exact .inr (.inl ⟨_, .core (.beginStoreCellValue read)⟩)
          | storeCellApply found =>
              obtain ⟨updatedStore, written⟩ :=
                storeTyping.write_exists (value := value) found
              exact .inr (.inl ⟨_, .core (.applyStoreCell written)⟩)
          | constructApply _ => exact .inr (.inl ⟨_, .core .applyConstruct⟩)
          | matchDataApply definitionLookup _ branchesTyping =>
              cases valueTyping with
              | constructed constructorLookup payloadTyping =>
                  obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
                    payloadTypeLookup⟩ :=
                      DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                        constructorLookup
                  have typedDefinitionLookup :=
                    DataEnvironment.lookupDataType?_eq_some_iff.mp definitionLookup
                  rw [typedDefinitionLookup] at runtimeDefinitionLookup
                  cases runtimeDefinitionLookup
                  obtain ⟨branch, branchLookup⟩ :=
                    branchesTyping.branch_exists payloadTypeLookup
                  exact .inr (.inl ⟨_, .core (.chooseData rfl branchLookup)⟩)
          | applyArgument =>
              cases valueTyping with
              | closure => exact .inr (.inl ⟨_, .core .beginArgument⟩)
              | hostFunction => exact .inr (.inl ⟨_, .beginApplication⟩)
          | applyClosure => exact .inr (.inl ⟨_, .core .invokeClosure⟩)
          | hostApply =>
              exact .inr (.inr (typed_hostApplication_emits valueTyping))
          | letBody => exact .inr (.inl ⟨_, .core .bindLet⟩)
          | ifBranches =>
              cases valueTyping with
              | bool =>
                  rename_i decision
                  cases decision with
                  | false => exact .inr (.inl ⟨_, .core .chooseFalse⟩)
                  | true => exact .inr (.inl ⟨_, .core .chooseTrue⟩)

theorem well_typed_host_state_never_faults
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : HostStateHasType state resultType definitions) :
    hostAdvance state ≠ .fault error := by
  intro faulted
  rcases host_state_progress stateTyping with
    ⟨value, store, rfl⟩ | ⟨next, step⟩ | ⟨suspension, emission⟩
  · simp [hostAdvance, advance, State.final] at faulted
  · rw [hostAdvance_next_iff.mpr step] at faulted
    contradiction
  · rw [hostAdvance_suspended_iff.mpr emission] at faulted
    contradiction

end Solcore.Core
end
