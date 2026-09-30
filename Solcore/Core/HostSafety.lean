import Solcore.Core.Host
import Solcore.Core.RuntimeStoreSafety

/-! Runtime value typing extended additively with fixed host capabilities. -/

set_option autoImplicit false

namespace Solcore.Core

mutual

  /-- Store-aware value typing that additionally admits host functions. -/
  inductive HostRuntimeValueHasType
      (world : StoreTyping) :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} :
        HostRuntimeValueHasType world .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        HostRuntimeValueHasType world (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        HostRuntimeValueHasType world (.word value) .word definitions
    | hostFunction
        {definitions : DataEnvironment} {function : HostFunction} :
        HostRuntimeValueHasType world
          (.hostFunction function) function.functionType definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world left leftType definitions →
        HostRuntimeValueHasType world right rightType definitions →
        HostRuntimeValueHasType world
          (.pair left right) (.product leftType rightType) definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world payload leftType definitions →
        HostRuntimeValueHasType world
          (.inLeft rightType payload) (.sum leftType rightType) definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world payload rightType definitions →
        HostRuntimeValueHasType world
          (.inRight leftType payload) (.sum leftType rightType) definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        HostRuntimeEnvironmentHasTypes world environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        HostRuntimeValueHasType world
          (.closure parameterType resultType body environment)
          (.function parameterType resultType) definitions
    | cellRef
        {definitions : DataEnvironment}
        {elementType : Ty} {location : Location} :
        world[location]? = some elementType →
        HostRuntimeValueHasType world
          (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        HostRuntimeValueHasType world payload payloadType definitions →
        HostRuntimeValueHasType world
          (.constructed constructor payload) (.namedData constructor.owner)
          definitions

  /-- Positional typing for environments that may contain host functions. -/
  inductive HostRuntimeEnvironmentHasTypes
      (world : StoreTyping) :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} :
        HostRuntimeEnvironmentHasTypes world [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        HostRuntimeValueHasType world value type definitions →
        HostRuntimeEnvironmentHasTypes world environment context definitions →
        HostRuntimeEnvironmentHasTypes world
          (value :: environment) (type :: context) definitions

end

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
  | unit | bool | word | hostFunction | pair | inLeft | inRight | closure
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
  | unit | bool | word | hostFunction | closure | cellRef | constructed => rfl
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
  | unit | bool | word | hostFunction | pair | inLeft | inRight | closure
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
  | product leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          exact .pair (leftIH leftTyping) (rightIH rightTyping)
  | sum leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | inLeft payloadTyping => exact .inLeft (leftIH payloadTyping)
      | inRight payloadTyping => exact .inRight (rightIH payloadTyping)

/-- The Core-local store may hold closures that capture host capabilities.
Cell references are checked against the world without recursively following them,
so this relation also supports cycles through cells. -/
structure HostStoreHasTypes
    (world : StoreTyping) (store : Store)
    (definitions : DataEnvironment := []) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        HostRuntimeValueHasType world value elementType definitions

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
