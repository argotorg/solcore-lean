import Solcore.Core.RuntimeTyping
import Solcore.Core.Correspondence

/-!
# Support for preservation

Laws of the relations in `RuntimeTyping`: lookup, weakening, store reads, writes and allocation,
and result types of the primitives. `Safety` rests on these.
-/

set_option autoImplicit false

namespace Solcore.Core

theorem EnvironmentHasTypes.lookup
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    (hasTypes : EnvironmentHasTypes environment context definitions)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧ ValueHasType value type definitions := by
  induction hasTypes using EnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef
  | constructed =>
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

theorem ValueHasType.bool_shape
    {definitions : DataEnvironment}
    {value : Value}
    (typing : ValueHasType value .bool definitions) :
    ∃ decision, value = .bool decision := by
  cases typing with
  | bool => exact ⟨_, rfl⟩

theorem ValueHasType.type_eq
    {definitions : DataEnvironment}
    {value : Value} {type : Ty}
    (typing : ValueHasType value type definitions) :
    value.type = type := by
  induction typing using ValueHasType.rec
      (motive_2 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | closure | cellRef | constructed => rfl
  | pair _ _ leftIH rightIH => simp [Value.type, leftIH, rightIH]
  | inLeft _ payloadIH => simp [Value.type, payloadIH]
  | inRight _ payloadIH => simp [Value.type, payloadIH]
  | nil | cons => exact True.intro

theorem unary_apply_result_has_type
    {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result)
    (definitions : DataEnvironment := []) :
    ValueHasType result op.resultType definitions := by
  have resultType := UnaryOp.apply_result_type applied
  clear applied operand
  cases op <;> cases result <;>
    simp [Value.type, UnaryOp.resultType] at resultType
  all_goals constructor

theorem binary_apply_result_has_type
    {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result)
    (definitions : DataEnvironment := []) :
    ValueHasType result op.resultType definitions := by
  have resultType := BinaryOp.apply_result_type applied
  clear applied left right
  cases op <;> cases result <;>
    simp [Value.type, BinaryOp.resultType] at resultType
  all_goals constructor

theorem ternary_apply_result_has_type
    {op : TernaryOp} {first second third result : Value}
    (applied : op.apply first second third = some result)
    (definitions : DataEnvironment := []) :
    ValueHasType result op.resultType definitions := by
  have resultType := TernaryOp.apply_result_type applied
  clear applied first second third
  cases op <;> cases result <;>
    simp [Value.type, TernaryOp.resultType] at resultType
  all_goals constructor

namespace WorldExtends

theorem refl (world : StoreTyping) : WorldExtends world world :=
  ⟨[], by simp⟩

theorem trans
    {first second third : StoreTyping}
    (firstSecond : WorldExtends first second)
    (secondThird : WorldExtends second third) :
    WorldExtends first third := by
  obtain ⟨middleSuffix, rfl⟩ := firstSecond
  obtain ⟨finalSuffix, rfl⟩ := secondThird
  exact ⟨middleSuffix ++ finalSuffix, by simp [List.append_assoc]⟩

theorem lookup
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {location : Location} {type : Ty}
    (found : initial[location]? = some type) :
    future[location]? = some type := by
  obtain ⟨suffix, rfl⟩ := extension
  have inBounds : location < initial.length :=
    (List.getElem?_eq_some_iff.mp found).1
  rw [List.getElem?_append_left (l₂ := suffix) inBounds]
  exact found

theorem length_le
    {initial future : StoreTyping}
    (extension : WorldExtends initial future) :
    initial.length ≤ future.length := by
  obtain ⟨suffix, rfl⟩ := extension
  simp

end WorldExtends

theorem RuntimeEnvironmentHasTypes.lookup
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (hasTypes : RuntimeEnvironmentHasTypes world environment context definitions)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧
        RuntimeValueHasType world value type definitions := by
  induction hasTypes using RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef
  | constructed =>
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

theorem RuntimeValueHasType.erase
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type definitions) :
    ValueHasType value type definitions := by
  apply RuntimeValueHasType.rec
      (world := world)
      (motive_1 := fun value type relationDefinitions _ =>
        ValueHasType value type relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        EnvironmentHasTypes environment context relationDefinitions)
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
  case cellRef => intros; exact .cellRef
  case constructed =>
    intro _ _ _ _ lookup _ payloadIH
    exact .constructed lookup payloadIH
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH
    exact .cons valueIH environmentIH

theorem RuntimeEnvironmentHasTypes.erase
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes world environment context definitions) :
    EnvironmentHasTypes environment context definitions := by
  apply RuntimeEnvironmentHasTypes.rec
      (world := world)
      (motive_1 := fun value type relationDefinitions _ =>
        ValueHasType value type relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        EnvironmentHasTypes environment context relationDefinitions)
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
  case cellRef => intros; exact .cellRef
  case constructed =>
    intro _ _ _ _ lookup _ payloadIH
    exact .constructed lookup payloadIH
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH
    exact .cons valueIH environmentIH

theorem RuntimeValueHasType.type_eq
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type definitions) :
    value.type = type :=
  typing.erase.type_eq

/-- Deep runtime-environment typing determines the same shallow type tags used
by executable entry guards. -/
theorem RuntimeEnvironmentHasTypes.type_tags
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes world environment context definitions) :
    environment.map Value.type = context := by
  induction typing using RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef
  | constructed =>
      trivial
  | nil => rfl
  | cons head _ _ tailIH =>
      simp only [List.map_cons, head.type_eq, tailIH]

theorem RuntimeValueHasType.bool_shape
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value}
    (typing : RuntimeValueHasType world value .bool definitions) :
    ∃ decision, value = .bool decision := by
  cases typing with
  | bool => exact ⟨_, rfl⟩

theorem RuntimeValueHasType.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {value : Value} {type : Ty}
    (typing : RuntimeValueHasType initial value type definitions) :
    RuntimeValueHasType future value type definitions := by
  apply RuntimeValueHasType.rec
      (world := initial)
      (motive_1 := fun value type relationDefinitions _ =>
        RuntimeValueHasType future value type relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        RuntimeEnvironmentHasTypes future environment context relationDefinitions)
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
    exact .cellRef (extension.lookup found)
  case constructed =>
    intro _ _ _ _ lookup _ payloadIH
    exact .constructed lookup payloadIH
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH
    exact .cons valueIH environmentIH

theorem RuntimeEnvironmentHasTypes.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes initial environment context definitions) :
    RuntimeEnvironmentHasTypes future environment context definitions := by
  apply RuntimeEnvironmentHasTypes.rec
      (world := initial)
      (motive_1 := fun value type relationDefinitions _ =>
        RuntimeValueHasType future value type relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        RuntimeEnvironmentHasTypes future environment context relationDefinitions)
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
    exact .cellRef (extension.lookup found)
  case constructed =>
    intro _ _ _ _ lookup _ payloadIH
    exact .constructed lookup payloadIH
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH
    exact .cons valueIH environmentIH

namespace RuntimeStoreHasTypes

theorem nil (definitions : DataEnvironment := []) :
    RuntimeStoreHasTypes [] [] definitions where
  length_eq := rfl
  lookup := by simp

theorem read
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    ∃ value,
      store.read? location = some value ∧
      RuntimeValueHasType world value elementType definitions :=
  typing.lookup found

theorem location_lt
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    location < store.length := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa [← typing.length_eq] using bound

/-- A fixed store determines its world without traversing referenced cells. -/
theorem world_eq
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions) :
    world = store.map Value.type := by
  apply List.ext_getElem (by simpa using typing.length_eq)
  intro index worldBound storeBound
  obtain ⟨value, found, valueTyped⟩ := typing.lookup
    (List.getElem?_eq_getElem worldBound)
  have read : store[index]? = some value := found
  have inBounds : index < store.length := by simpa using storeBound
  have valueEq : store[index] = value :=
    Option.some.inj ((List.getElem?_eq_getElem inBounds).symm.trans read)
  simpa [valueEq] using valueTyped.type_eq.symm

theorem allocate
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {elementType : Ty} {value : Value}
    (valueTyping : RuntimeValueHasType world value elementType definitions) :
    RuntimeStoreHasTypes (world ++ [elementType])
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
        have bound := (List.getElem?_eq_some_iff.mp foundType).1
        have upper : location ≤ world.length := by
          apply Nat.lt_succ_iff.mp
          simpa using bound
        exact Nat.le_antisymm upper (Nat.le_of_not_gt old)
      subst location
      have storedTypeEq : storedType = elementType := by
        exact (Option.some.inj (by simpa using foundType)).symm
      subst storedType
      exact ⟨value,
        by simpa [← typing.length_eq] using Store.allocate_fresh_lookup store value,
        valueTyping.weaken extension⟩

theorem write
    {definitions : DataEnvironment} {world : StoreTyping}
    {store updatedStore : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType)
    (valueTyping : RuntimeValueHasType world value elementType definitions)
    (written : store.write? location value = some updatedStore) :
    RuntimeStoreHasTypes world updatedStore definitions := by
  constructor
  · rw [Store.write?_preserves_length written]
    exact typing.length_eq
  · intro otherLocation otherType otherFound
    obtain ⟨oldValue, oldLookup, oldTyping⟩ := typing.lookup otherFound
    by_cases same : otherLocation = location
    · subst otherLocation
      have typeEq := Option.some.inj (found.symm.trans otherFound)
      subst otherType
      exact ⟨value, Store.write?_reads_written written, valueTyping⟩
    · exact ⟨oldValue,
        (Store.write?_preserves_other written same).trans oldLookup, oldTyping⟩

theorem write_exists
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType) :
    ∃ updatedStore, store.write? location value = some updatedStore :=
  (Store.write?_success_iff store location value).2 (typing.location_lt found)

end RuntimeStoreHasTypes

namespace StoreHasTypes

theorem nil : StoreHasTypes [] [] where
  length_eq := rfl
  lookup := by simp

theorem read
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    ∃ value,
      store.read? location = some value ∧
      CellPayload elementType ∧
      ValueHasType value elementType :=
  typing.lookup found

theorem location_lt
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    location < store.length := by
  have worldBound : location < world.length :=
    (List.getElem?_eq_some_iff.mp found).1
  simpa [← typing.length_eq] using worldBound

theorem allocate
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    {elementType : Ty} {value : Value}
    (payload : CellPayload elementType)
    (valueTyping : ValueHasType value elementType) :
    StoreHasTypes (world ++ [elementType]) (store.allocate value).1 := by
  constructor
  · simp [typing.length_eq]
  · intro location storedType foundType
    by_cases old : location < world.length
    · have oldType : world[location]? = some storedType := by
        rw [List.getElem?_append_left (l₂ := [elementType]) old] at foundType
        exact foundType
      obtain ⟨oldValue, oldLookup, oldPayload, oldTyping⟩ := typing.lookup oldType
      have storeOld : location < store.length := by
        simpa [← typing.length_eq] using old
      exact ⟨oldValue,
        (Store.allocate_old_lookup store value storeOld).trans oldLookup,
        oldPayload, oldTyping⟩
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
        payload, valueTyping⟩

theorem write
    {world : StoreTyping} {store updatedStore : Store}
    (typing : StoreHasTypes world store)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType)
    (valueTyping : ValueHasType value elementType)
    (written : store.write? location value = some updatedStore) :
    StoreHasTypes world updatedStore := by
  constructor
  · rw [Store.write?_preserves_length written]
    exact typing.length_eq
  · intro otherLocation otherType otherFound
    obtain ⟨oldValue, oldLookup, payload, oldTyping⟩ := typing.lookup otherFound
    by_cases same : otherLocation = location
    · subst otherLocation
      have typeEq : elementType = otherType :=
        Option.some.inj (found.symm.trans otherFound)
      subst typeEq
      exact ⟨value, Store.write?_reads_written written, payload, valueTyping⟩
    · exact ⟨oldValue,
        (Store.write?_preserves_other written same).trans oldLookup,
        payload, oldTyping⟩

theorem write_exists
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType) :
    ∃ updatedStore, store.write? location value = some updatedStore :=
  (Store.write?_success_iff store location value).2 (typing.location_lt found)

end StoreHasTypes

theorem CellPayload.valueHasType_rebase
    {elementType : Ty}
    (payload : CellPayload elementType)
    {sourceDefinitions targetDefinitions : DataEnvironment}
    {value : Value}
    (typing : ValueHasType value elementType sourceDefinitions) :
    ValueHasType value elementType targetDefinitions := by
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

theorem CellPayload.runtimeValueHasType
    {elementType : Ty}
    (payload : CellPayload elementType)
    {world : StoreTyping} {value : Value}
    (typing : ValueHasType value elementType)
    (definitions : DataEnvironment := []) :
    RuntimeValueHasType world value elementType definitions := by
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

/-- Existing first-order stores embed without changing their locations. -/
theorem StoreHasTypes.toRuntime
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    (definitions : DataEnvironment := []) :
    RuntimeStoreHasTypes world store definitions where
  length_eq := typing.length_eq
  lookup := by
    intro location elementType found
    obtain ⟨value, read, payload, valueTyping⟩ := typing.lookup found
    exact ⟨value, read, payload.runtimeValueHasType valueTyping definitions⟩

theorem unary_apply_result_has_runtime_type
    {world : StoreTyping} {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result)
    (definitions : DataEnvironment := []) :
    RuntimeValueHasType world result op.resultType definitions := by
  apply CellPayload.runtimeValueHasType
    (elementType := op.resultType)
    (definitions := definitions)
    (typing := unary_apply_result_has_type applied (definitions := []))
  cases op <;> constructor

theorem binary_apply_result_has_runtime_type
    {world : StoreTyping} {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result)
    (definitions : DataEnvironment := []) :
    RuntimeValueHasType world result op.resultType definitions := by
  apply CellPayload.runtimeValueHasType
    (elementType := op.resultType)
    (definitions := definitions)
    (typing := binary_apply_result_has_type applied (definitions := []))
  cases op <;> constructor

theorem ternary_apply_result_has_runtime_type
    {world : StoreTyping} {op : TernaryOp}
    {first second third result : Value}
    (applied : op.apply first second third = some result)
    (definitions : DataEnvironment := []) :
    RuntimeValueHasType world result op.resultType definitions := by
  apply CellPayload.runtimeValueHasType
    (elementType := op.resultType)
    (definitions := definitions)
    (typing := ternary_apply_result_has_type applied (definitions := []))
  cases op <;> constructor

theorem BranchesHaveType.lookup
    {definitions : DataEnvironment}
    {context : Context} {resultType : Ty}
    {payloadTypes : List Ty} {branches : List Expr}
    (typing :
      BranchesHaveType context resultType payloadTypes branches definitions)
    {index : Nat} {payloadType : Ty} {branch : Expr}
    (payloadLookup : payloadTypes[index]? = some payloadType)
    (branchLookup : branches[index]? = some branch) :
    HasType (payloadType :: context) branch resultType definitions := by
  induction typing using BranchesHaveType.rec
      (motive_1 := fun _ _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | var | pair | first | second | lambda | apply
  | inLeft | inRight | caseE | newCell | loadCell | storeCell | construct
  | matchData | unary | binary | ternary | letE | ifE =>
      exact True.intro
  | nil => simp at payloadLookup
  | cons headTyping _ _ tailIH =>
      cases index with
      | zero =>
          simp at payloadLookup branchLookup
          cases payloadLookup
          cases branchLookup
          exact headTyping
      | succ index =>
          apply tailIH
          · simpa using payloadLookup
          · simpa using branchLookup

theorem BranchesHaveType.length_eq
    {definitions : DataEnvironment}
    {context : Context} {resultType : Ty}
    {payloadTypes : List Ty} {branches : List Expr}
    (typing :
      BranchesHaveType context resultType payloadTypes branches definitions) :
    payloadTypes.length = branches.length := by
  induction typing using BranchesHaveType.rec
      (motive_1 := fun _ _ _ _ _ => True) with
  | unit | bool | word | integer | var | pair | first | second | lambda | apply
  | inLeft | inRight | caseE | newCell | loadCell | storeCell | construct
  | matchData | unary | binary | ternary | letE | ifE =>
      exact True.intro
  | nil => rfl
  | cons _ _ _ tailIH => simp [tailIH]

theorem BranchesHaveType.branch_exists
    {definitions : DataEnvironment}
    {context : Context} {resultType : Ty}
    {payloadTypes : List Ty} {branches : List Expr}
    (typing :
      BranchesHaveType context resultType payloadTypes branches definitions)
    {index : Nat} {payloadType : Ty}
    (payloadLookup : payloadTypes[index]? = some payloadType) :
    ∃ branch, branches[index]? = some branch := by
  have payloadBound : index < payloadTypes.length :=
    (List.getElem?_eq_some_iff.mp payloadLookup).1
  have branchBound : index < branches.length := by
    simpa [← typing.length_eq] using payloadBound
  exact ⟨branches[index], List.getElem?_eq_getElem _⟩

theorem FrameHasType.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {frame : Frame} {inputType outputType : Ty}
    (typing : FrameHasType initial frame inputType outputType definitions) :
    FrameHasType future frame inputType outputType definitions := by
  cases typing with
  | unaryApply => exact .unaryApply
  | binaryRight environmentTyping rightTyping =>
      exact .binaryRight (environmentTyping.weaken extension) rightTyping
  | binaryApply leftTyping =>
      exact .binaryApply (leftTyping.weaken extension)
  | ternarySecond environmentTyping secondTyping thirdTyping =>
      exact .ternarySecond (environmentTyping.weaken extension)
        secondTyping thirdTyping
  | ternaryThird firstTyping environmentTyping thirdTyping =>
      exact .ternaryThird (firstTyping.weaken extension)
        (environmentTyping.weaken extension) thirdTyping
  | ternaryApply firstTyping secondTyping =>
      exact .ternaryApply (firstTyping.weaken extension)
        (secondTyping.weaken extension)
  | pairRight environmentTyping rightTyping =>
      exact .pairRight (environmentTyping.weaken extension) rightTyping
  | pairApply leftTyping =>
      exact .pairApply (leftTyping.weaken extension)
  | firstApply => exact .firstApply
  | secondApply => exact .secondApply
  | inLeftApply => exact .inLeftApply
  | inRightApply => exact .inRightApply
  | caseBranches environmentTyping leftTyping rightTyping =>
      exact .caseBranches (environmentTyping.weaken extension)
        leftTyping rightTyping
  | newCellApply => exact .newCellApply
  | loadCellApply => exact .loadCellApply
  | storeCellValue environmentTyping valueTyping =>
      exact .storeCellValue (environmentTyping.weaken extension)
        valueTyping
  | storeCellApply found =>
      exact .storeCellApply (extension.lookup found)
  | constructApply lookup => exact .constructApply lookup
  | matchDataApply definitionLookup environmentTyping branchesTyping =>
      exact .matchDataApply definitionLookup
        (environmentTyping.weaken extension) branchesTyping
  | applyArgument environmentTyping argumentTyping =>
      exact .applyArgument (environmentTyping.weaken extension) argumentTyping
  | applyClosure environmentTyping bodyTyping =>
      exact .applyClosure (environmentTyping.weaken extension) bodyTyping
  | letBody environmentTyping bodyTyping =>
      exact .letBody (environmentTyping.weaken extension) bodyTyping
  | ifBranches environmentTyping thenTyping elseTyping =>
      exact .ifBranches (environmentTyping.weaken extension)
        thenTyping elseTyping

theorem ContinuationHasType.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {continuation : List Frame} {inputType outputType : Ty}
    (typing :
      ContinuationHasType initial continuation inputType outputType definitions) :
    ContinuationHasType future continuation inputType outputType definitions := by
  induction typing with
  | nil => exact .nil
  | cons frameTyping _ tailIH =>
      exact .cons (frameTyping.weaken extension) tailIH

end Solcore.Core
