import Solcore.Core.Correspondence

set_option autoImplicit false

namespace Solcore.Core

/-! ## Structural value typing -/

mutual

  inductive ValueHasType : Value → Ty → Prop where
    | unit : ValueHasType .unit .unit
    | bool {value : Bool} : ValueHasType (.bool value) .bool
    | word {value : Word} : ValueHasType (.word value) .word
    | pair
        {left right : Value} {leftType rightType : Ty} :
        ValueHasType left leftType →
        ValueHasType right rightType →
        ValueHasType (.pair left right) (.product leftType rightType)
    | inLeft
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload leftType →
        ValueHasType (.inLeft rightType payload) (.sum leftType rightType)
    | inRight
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload rightType →
        ValueHasType (.inRight leftType payload) (.sum leftType rightType)
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        EnvironmentHasTypes environment context →
        HasType (parameterType :: context) body resultType →
        ValueHasType
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
    | cellRef {elementType : Ty} {location : Location} :
        ValueHasType (.cellRef elementType location) (.cell elementType)

  inductive EnvironmentHasTypes : Environment → Context → Prop where
    | nil : EnvironmentHasTypes [] []
    | cons
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        ValueHasType value type →
        EnvironmentHasTypes environment context →
        EnvironmentHasTypes (value :: environment) (type :: context)

end

theorem EnvironmentHasTypes.lookup
    {environment : Environment} {context : Context}
    (hasTypes : EnvironmentHasTypes environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value, environment[index]? = some value ∧ ValueHasType value type := by
  induction hasTypes using EnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ => True) generalizing index with
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef =>
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
    {value : Value}
    (typing : ValueHasType value .bool) :
    ∃ decision, value = .bool decision := by
  cases typing with
  | bool => exact ⟨_, rfl⟩

theorem ValueHasType.type_eq
    {value : Value} {type : Ty}
    (typing : ValueHasType value type) :
    value.type = type := by
  induction typing using ValueHasType.rec
      (motive_2 := fun _ _ _ => True) with
  | unit | bool | word | closure | cellRef => rfl
  | pair _ _ leftIH rightIH => simp [Value.type, leftIH, rightIH]
  | inLeft _ payloadIH => simp [Value.type, payloadIH]
  | inRight _ payloadIH => simp [Value.type, payloadIH]
  | nil | cons => exact True.intro

theorem unary_apply_result_has_type
    {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    ValueHasType result op.resultType := by
  cases op <;> cases operand <;>
    simp [UnaryOp.apply] at applied <;>
    cases applied <;> constructor

theorem binary_apply_result_has_type
    {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    ValueHasType result op.resultType := by
  cases op <;> cases left <;> cases right <;>
    simp [BinaryOp.apply] at applied <;>
    cases applied <;> constructor

/-! ## Worlds, runtime typing, and typed stores -/

def WorldExtends (initial future : StoreTyping) : Prop :=
  ∃ suffix, future = initial ++ suffix

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

mutual

  inductive RuntimeValueHasType
      (world : StoreTyping) : Value → Ty → Prop where
    | unit : RuntimeValueHasType world .unit .unit
    | bool {value : Bool} : RuntimeValueHasType world (.bool value) .bool
    | word {value : Word} : RuntimeValueHasType world (.word value) .word
    | pair
        {left right : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world left leftType →
        RuntimeValueHasType world right rightType →
        RuntimeValueHasType world (.pair left right) (.product leftType rightType)
    | inLeft
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload leftType →
        RuntimeValueHasType world
          (.inLeft rightType payload) (.sum leftType rightType)
    | inRight
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload rightType →
        RuntimeValueHasType world
          (.inRight leftType payload) (.sum leftType rightType)
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        RuntimeEnvironmentHasTypes world environment context →
        HasType (parameterType :: context) body resultType →
        RuntimeValueHasType world
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
    | cellRef
        {elementType : Ty} {location : Location} :
        world[location]? = some elementType →
        RuntimeValueHasType world
          (.cellRef elementType location) (.cell elementType)

  inductive RuntimeEnvironmentHasTypes
      (world : StoreTyping) : Environment → Context → Prop where
    | nil : RuntimeEnvironmentHasTypes world [] []
    | cons
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        RuntimeValueHasType world value type →
        RuntimeEnvironmentHasTypes world environment context →
        RuntimeEnvironmentHasTypes world
          (value :: environment) (type :: context)

end

theorem RuntimeEnvironmentHasTypes.lookup
    {world : StoreTyping} {environment : Environment} {context : Context}
    (hasTypes : RuntimeEnvironmentHasTypes world environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧ RuntimeValueHasType world value type := by
  induction hasTypes using RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ => True) generalizing index with
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef =>
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
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type) :
    ValueHasType value type := by
  induction typing using RuntimeValueHasType.rec
      (motive_2 := fun environment context _ =>
        EnvironmentHasTypes environment context) with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | inLeft _ payloadIH => exact .inLeft payloadIH
  | inRight _ payloadIH => exact .inRight payloadIH
  | closure _ bodyTyping environmentIH =>
      exact .closure environmentIH bodyTyping
  | cellRef => exact .cellRef
  | nil => exact .nil
  | cons _ _ valueIH environmentIH => exact .cons valueIH environmentIH

theorem RuntimeEnvironmentHasTypes.erase
    {world : StoreTyping} {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes world environment context) :
    EnvironmentHasTypes environment context := by
  cases typing with
  | nil => exact .nil
  | cons valueTyping environmentTyping =>
      exact .cons valueTyping.erase environmentTyping.erase
termination_by environment

theorem RuntimeValueHasType.type_eq
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type) :
    value.type = type :=
  typing.erase.type_eq

theorem RuntimeValueHasType.bool_shape
    {world : StoreTyping} {value : Value}
    (typing : RuntimeValueHasType world value .bool) :
    ∃ decision, value = .bool decision := by
  cases typing with
  | bool => exact ⟨_, rfl⟩

theorem RuntimeValueHasType.weaken
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {value : Value} {type : Ty}
    (typing : RuntimeValueHasType initial value type) :
    RuntimeValueHasType future value type := by
  induction typing using RuntimeValueHasType.rec
      (motive_2 := fun environment context _ =>
        RuntimeEnvironmentHasTypes future environment context) with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | inLeft _ payloadIH => exact .inLeft payloadIH
  | inRight _ payloadIH => exact .inRight payloadIH
  | closure _ bodyTyping environmentIH =>
      exact .closure environmentIH bodyTyping
  | cellRef found => exact .cellRef (extension.lookup found)
  | nil => exact .nil
  | cons _ _ valueIH environmentIH => exact .cons valueIH environmentIH

theorem RuntimeEnvironmentHasTypes.weaken
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes initial environment context) :
    RuntimeEnvironmentHasTypes future environment context := by
  cases typing with
  | nil => exact .nil
  | cons valueTyping environmentTyping =>
      exact .cons (valueTyping.weaken extension) (environmentTyping.weaken extension)
termination_by environment

structure StoreHasTypes (world : StoreTyping) (store : Store) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        CellPayload elementType ∧
        ValueHasType value elementType

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

theorem CellPayload.runtimeValueHasType
    {elementType : Ty}
    (payload : CellPayload elementType)
    {world : StoreTyping} {value : Value}
    (typing : ValueHasType value elementType) :
    RuntimeValueHasType world value elementType := by
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

theorem unary_apply_result_has_runtime_type
    {world : StoreTyping} {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    RuntimeValueHasType world result op.resultType := by
  apply CellPayload.runtimeValueHasType
    (elementType := op.resultType)
    (typing := unary_apply_result_has_type applied)
  cases op <;> constructor

theorem binary_apply_result_has_runtime_type
    {world : StoreTyping} {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    RuntimeValueHasType world result op.resultType := by
  apply CellPayload.runtimeValueHasType
    (elementType := op.resultType)
    (typing := binary_apply_result_has_type applied)
  cases op <;> constructor

/-! ## Preservation for the state-threaded evaluator -/

theorem evaluation_preserves_type
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store}
    {expr : Expr} {value : Value} {type : Ty} {world : StoreTyping}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (typing : HasType context expr type)
    (environmentTyping : RuntimeEnvironmentHasTypes world environment context)
    (storeTyping : StoreHasTypes world initialStore) :
    ∃ finalWorld,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type := by
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
      | inLeft payloadTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, valueTyping⟩ :=
            payloadIH payloadTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping, .inLeft valueTyping⟩
  | inRight _ payloadIH =>
      cases typing with
      | inRight payloadTyping =>
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
      | lambda bodyTyping =>
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
      | newCell initializerTyping payload =>
          obtain ⟨initializedWorld, initializerExtension,
            initializedStoreTyping, initialValueTyping⟩ :=
              initializerIH initializerTyping environmentTyping storeTyping
          let resultWorld := initializedWorld ++ [elementType]
          have resultStoreTyping :
              StoreHasTypes resultWorld
                (initializedStore.allocate initialValue).1 := by
            simpa [resultWorld] using
              initializedStoreTyping.allocate payload initialValueTyping.erase
          have freshLookup :
              resultWorld[(initializedStore.allocate initialValue).2]? =
                some elementType := by
            simp [resultWorld, ← initializedStoreTyping.length_eq]
          exact ⟨resultWorld,
            initializerExtension.trans ⟨[elementType], rfl⟩,
            resultStoreTyping, .cellRef freshLookup⟩
  | loadCell _ loaded referenceIH =>
      cases typing with
      | loadCell referenceTyping _ =>
          obtain ⟨referenceWorld, extension, referenceStoreTyping,
            referenceValueTyping⟩ :=
              referenceIH referenceTyping environmentTyping storeTyping
          cases referenceValueTyping with
          | cellRef found =>
              obtain ⟨storedValue, storedLookup, payload, storedTyping⟩ :=
                referenceStoreTyping.lookup found
              rw [loaded] at storedLookup
              cases storedLookup
              exact ⟨referenceWorld, extension, referenceStoreTyping,
                payload.runtimeValueHasType storedTyping⟩
  | storeCell _ _ _ written referenceIH valueIH =>
      cases typing with
      | storeCell referenceTyping valueTyping _ =>
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
                valueStoreTyping.write futureFound newValueTyping.erase written
              exact ⟨valueWorld, referenceExtension.trans valueExtension,
                resultStoreTyping, .unit⟩
  | unary _ applied operandIH =>
      cases typing with
      | unary operandTyping =>
          obtain ⟨resultWorld, extension, resultStoreTyping, _⟩ :=
            operandIH operandTyping environmentTyping storeTyping
          exact ⟨resultWorld, extension, resultStoreTyping,
            unary_apply_result_has_runtime_type applied⟩
  | binary _ _ applied leftIH rightIH =>
      cases typing with
      | binary leftTyping rightTyping =>
          obtain ⟨rightWorld, leftExtension, rightStoreTyping, _⟩ :=
            leftIH leftTyping environmentTyping storeTyping
          obtain ⟨resultWorld, rightExtension, resultStoreTyping, _⟩ :=
            rightIH rightTyping
              (environmentTyping.weaken leftExtension) rightStoreTyping
          exact ⟨resultWorld, leftExtension.trans rightExtension,
            resultStoreTyping, binary_apply_result_has_runtime_type applied⟩
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

/-! ## Stateful Kripke reducibility -/

def ReducibleValue
    (world : StoreTyping) : (type : Ty) → Value → Prop
  | .unit, value => value = .unit
  | .bool, value => ∃ decision, value = .bool decision
  | .word, value => ∃ word, value = .word word
  | .product leftType rightType, value =>
      ∃ left right,
        value = .pair left right ∧
        ReducibleValue world leftType left ∧
        ReducibleValue world rightType right
  | .sum leftType rightType, value =>
      (∃ payload,
        value = .inLeft rightType payload ∧
        ReducibleValue world leftType payload) ∨
      (∃ payload,
        value = .inRight leftType payload ∧
        ReducibleValue world rightType payload)
  | .function parameterType resultType, value =>
      ∃ body environment context,
        value = .closure parameterType resultType body environment ∧
        RuntimeEnvironmentHasTypes world environment context ∧
        HasType (parameterType :: context) body resultType ∧
        ∀ {futureWorld : StoreTyping} {futureStore : Store}
            {argument : Value},
          WorldExtends world futureWorld →
          StoreHasTypes futureWorld futureStore →
          ReducibleValue futureWorld parameterType argument →
          ∃ finalWorld finalStore result,
            WorldExtends futureWorld finalWorld ∧
            StoreHasTypes finalWorld finalStore ∧
            Evaluates (argument :: environment) futureStore body result finalStore ∧
            ReducibleValue finalWorld resultType result
  | .cell elementType, value =>
      ∃ location,
        value = .cellRef elementType location ∧
        world[location]? = some elementType
termination_by type _ => type

inductive ReducibleEnvironment
    (world : StoreTyping) : Environment → Context → Prop where
  | nil : ReducibleEnvironment world [] []
  | cons
      {value : Value} {type : Ty}
      {environment : Environment} {context : Context} :
      ReducibleValue world type value →
      ReducibleEnvironment world environment context →
      ReducibleEnvironment world (value :: environment) (type :: context)

theorem ReducibleEnvironment.lookup
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧ ReducibleValue world type value := by
  induction reducible generalizing index with
  | nil => simp at typeLookup
  | cons headReducible _ tailIH =>
      cases index with
      | zero =>
          simp at typeLookup
          cases typeLookup
          exact ⟨_, rfl, headReducible⟩
      | succ index =>
          simp at typeLookup
          obtain ⟨value, valueLookup, valueReducible⟩ := tailIH typeLookup
          exact ⟨value, by simpa using valueLookup, valueReducible⟩

theorem ReducibleValue.runtimeHasType
    {world : StoreTyping} {type : Ty} {value : Value}
    (reducible : ReducibleValue world type value) :
    RuntimeValueHasType world value type := by
  induction type generalizing value with
  | unit =>
      simp only [ReducibleValue] at reducible
      subst value
      exact .unit
  | bool =>
      simp only [ReducibleValue] at reducible
      obtain ⟨decision, rfl⟩ := reducible
      exact .bool
  | word =>
      simp only [ReducibleValue] at reducible
      obtain ⟨word, rfl⟩ := reducible
      exact .word
  | product leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible
      obtain ⟨left, right, rfl, leftReducible, rightReducible⟩ := reducible
      exact .pair (leftIH leftReducible) (rightIH rightReducible)
  | sum leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible
      cases reducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          exact .inLeft (leftIH payloadReducible)
      | inr rightReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := rightReducible
          exact .inRight (rightIH payloadReducible)
  | function parameterType resultType _ _ =>
      simp only [ReducibleValue] at reducible
      obtain ⟨body, environment, context, rfl,
        environmentTyping, bodyTyping, _⟩ := reducible
      exact .closure environmentTyping bodyTyping
  | cell elementType _ =>
      simp only [ReducibleValue] at reducible
      obtain ⟨location, rfl, found⟩ := reducible
      exact .cellRef found

theorem ReducibleValue.hasType
    {world : StoreTyping} {type : Ty} {value : Value}
    (reducible : ReducibleValue world type value) :
    ValueHasType value type :=
  reducible.runtimeHasType.erase

theorem ReducibleEnvironment.runtimeHasTypes
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context) :
    RuntimeEnvironmentHasTypes world environment context := by
  induction reducible with
  | nil => exact .nil
  | cons headReducible _ tailIH =>
      exact .cons headReducible.runtimeHasType tailIH

theorem ReducibleEnvironment.hasTypes
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context) :
    EnvironmentHasTypes environment context :=
  reducible.runtimeHasTypes.erase

theorem ReducibleValue.weaken
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {type : Ty} {value : Value}
    (reducible : ReducibleValue initial type value) :
    ReducibleValue future type value := by
  induction type generalizing value with
  | unit => simpa only [ReducibleValue] using reducible
  | bool => simpa only [ReducibleValue] using reducible
  | word => simpa only [ReducibleValue] using reducible
  | product leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible ⊢
      obtain ⟨left, right, rfl, leftReducible, rightReducible⟩ := reducible
      exact ⟨left, right, rfl, leftIH leftReducible, rightIH rightReducible⟩
  | sum leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible ⊢
      cases reducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          exact .inl ⟨payload, rfl, leftIH payloadReducible⟩
      | inr rightReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := rightReducible
          exact .inr ⟨payload, rfl, rightIH payloadReducible⟩
  | function parameterType resultType _ _ =>
      simp only [ReducibleValue] at reducible ⊢
      obtain ⟨body, environment, context, rfl,
        environmentTyping, bodyTyping, callable⟩ := reducible
      exact ⟨body, environment, context, rfl,
        environmentTyping.weaken extension, bodyTyping,
        fun futureExtension futureStoreTyping argumentReducible =>
          callable (extension.trans futureExtension)
            futureStoreTyping argumentReducible⟩
  | cell elementType _ =>
      simp only [ReducibleValue] at reducible ⊢
      obtain ⟨location, rfl, found⟩ := reducible
      exact ⟨location, rfl, extension.lookup found⟩

theorem ReducibleEnvironment.weaken
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment initial environment context) :
    ReducibleEnvironment future environment context := by
  induction reducible with
  | nil => exact .nil
  | cons headReducible _ tailIH =>
      exact .cons (headReducible.weaken extension) tailIH

theorem CellPayload.reducible
    {elementType : Ty}
    (payload : CellPayload elementType)
    {world : StoreTyping} {value : Value}
    (typing : ValueHasType value elementType) :
    ReducibleValue world elementType value := by
  induction payload generalizing value with
  | unit =>
      cases typing
      simp only [ReducibleValue]
  | bool =>
      cases typing with
      | bool =>
          simp only [ReducibleValue]
          exact ⟨_, rfl⟩
  | word =>
      cases typing with
      | word =>
          simp only [ReducibleValue]
          exact ⟨_, rfl⟩
  | product leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          simp only [ReducibleValue]
          exact ⟨_, _, rfl, leftIH leftTyping, rightIH rightTyping⟩
  | sum leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | inLeft payloadTyping =>
          simp only [ReducibleValue]
          exact .inl ⟨_, rfl, leftIH payloadTyping⟩
      | inRight payloadTyping =>
          simp only [ReducibleValue]
          exact .inr ⟨_, rfl, rightIH payloadTyping⟩

theorem unary_apply_result_reducible
    {world : StoreTyping} {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    ReducibleValue world op.resultType result := by
  apply CellPayload.reducible
    (typing := unary_apply_result_has_type applied)
  cases op <;> constructor

theorem binary_apply_result_reducible
    {world : StoreTyping} {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    ReducibleValue world op.resultType result := by
  apply CellPayload.reducible
    (typing := binary_apply_result_has_type applied)
  cases op <;> constructor

theorem reducibility_fundamental
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentReducible : ReducibleEnvironment world environment context)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      ReducibleValue finalWorld type value := by
  induction typing generalizing world environment store with
  | unit =>
      exact ⟨world, store, .unit, .refl world, storeTyping, .unit,
        by simp only [ReducibleValue]⟩
  | bool =>
      exact ⟨world, store, .bool _, .refl world, storeTyping, .bool,
        by simp only [ReducibleValue]; exact ⟨_, rfl⟩⟩
  | word =>
      exact ⟨world, store, .word _, .refl world, storeTyping, .word,
        by simp only [ReducibleValue]; exact ⟨_, rfl⟩⟩
  | var typeLookup =>
      obtain ⟨value, valueLookup, valueReducible⟩ :=
        environmentReducible.lookup typeLookup
      exact ⟨world, store, value, .refl world, storeTyping,
        .var valueLookup, valueReducible⟩
  | pair leftTyping rightTyping leftIH rightIH =>
      obtain ⟨leftWorld, leftStore, leftValue, leftExtension,
        leftStoreTyping, leftEvaluation, leftReducible⟩ :=
          leftIH environmentReducible storeTyping
      obtain ⟨rightWorld, rightStore, rightValue, rightExtension,
        rightStoreTyping, rightEvaluation, rightReducible⟩ :=
          rightIH (environmentReducible.weaken leftExtension) leftStoreTyping
      exact ⟨rightWorld, rightStore, .pair leftValue rightValue,
        leftExtension.trans rightExtension, rightStoreTyping,
        .pair leftEvaluation rightEvaluation,
        by
          simp only [ReducibleValue]
          exact ⟨leftValue, rightValue, rfl,
            leftReducible.weaken rightExtension, rightReducible⟩⟩
  | first operandTyping operandIH =>
      obtain ⟨resultWorld, resultStore, operandValue, extension,
        resultStoreTyping, operandEvaluation, operandReducible⟩ :=
          operandIH environmentReducible storeTyping
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl, leftReducible, _⟩ := operandReducible
      exact ⟨resultWorld, resultStore, leftValue, extension,
        resultStoreTyping, .first operandEvaluation, leftReducible⟩
  | second operandTyping operandIH =>
      obtain ⟨resultWorld, resultStore, operandValue, extension,
        resultStoreTyping, operandEvaluation, operandReducible⟩ :=
          operandIH environmentReducible storeTyping
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl, _, rightReducible⟩ := operandReducible
      exact ⟨resultWorld, resultStore, rightValue, extension,
        resultStoreTyping, .second operandEvaluation, rightReducible⟩
  | @lambda context parameterType resultType body bodyTyping bodyIH =>
      refine ⟨world, store,
        .closure parameterType resultType body environment,
        .refl world, storeTyping, .lambda, ?_⟩
      simp only [ReducibleValue]
      exact ⟨body, environment, context, rfl,
        environmentReducible.runtimeHasTypes, bodyTyping,
        fun futureExtension futureStoreTyping argumentReducible =>
          bodyIH
            (.cons argumentReducible
              (environmentReducible.weaken futureExtension))
            futureStoreTyping⟩
  | @apply context function argument parameterType resultType
      functionTyping argumentTyping functionIH argumentIH =>
      obtain ⟨functionWorld, functionStore, functionValue,
        functionExtension, functionStoreTyping, functionEvaluation,
        functionReducible⟩ :=
          functionIH environmentReducible storeTyping
      simp only [ReducibleValue] at functionReducible
      obtain ⟨body, capturedEnvironment, capturedContext, rfl,
        capturedTyping, bodyTyping, callable⟩ := functionReducible
      obtain ⟨argumentWorld, argumentStore, argumentValue,
        argumentExtension, argumentStoreTyping, argumentEvaluation,
        argumentReducible⟩ :=
          argumentIH (environmentReducible.weaken functionExtension)
            functionStoreTyping
      obtain ⟨resultWorld, resultStore, result, bodyExtension,
        resultStoreTyping, bodyEvaluation, resultReducible⟩ :=
          callable argumentExtension argumentStoreTyping argumentReducible
      exact ⟨resultWorld, resultStore, result,
        functionExtension.trans (argumentExtension.trans bodyExtension),
        resultStoreTyping,
        .apply functionEvaluation argumentEvaluation bodyEvaluation,
        resultReducible⟩
  | @inLeft context rightType leftType payload payloadTyping payloadIH =>
      obtain ⟨resultWorld, resultStore, payloadValue, extension,
        resultStoreTyping, payloadEvaluation, payloadReducible⟩ :=
          payloadIH environmentReducible storeTyping
      exact ⟨resultWorld, resultStore, .inLeft rightType payloadValue,
        extension, resultStoreTyping, .inLeft payloadEvaluation,
        by
          simp only [ReducibleValue]
          exact .inl ⟨payloadValue, rfl, payloadReducible⟩⟩
  | @inRight context leftType rightType payload payloadTyping payloadIH =>
      obtain ⟨resultWorld, resultStore, payloadValue, extension,
        resultStoreTyping, payloadEvaluation, payloadReducible⟩ :=
          payloadIH environmentReducible storeTyping
      exact ⟨resultWorld, resultStore, .inRight leftType payloadValue,
        extension, resultStoreTyping, .inRight payloadEvaluation,
        by
          simp only [ReducibleValue]
          exact .inr ⟨payloadValue, rfl, payloadReducible⟩⟩
  | @caseE context scrutinee leftBranch rightBranch
      leftType rightType resultType
      scrutineeTyping leftTyping rightTyping
      scrutineeIH leftIH rightIH =>
      obtain ⟨branchWorld, branchStore, scrutineeValue,
        scrutineeExtension, branchStoreTyping, scrutineeEvaluation,
        scrutineeReducible⟩ :=
          scrutineeIH environmentReducible storeTyping
      simp only [ReducibleValue] at scrutineeReducible
      cases scrutineeReducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              leftIH
                (.cons payloadReducible
                  (environmentReducible.weaken scrutineeExtension))
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            scrutineeExtension.trans branchExtension, resultStoreTyping,
            .caseLeft scrutineeEvaluation branchEvaluation, resultReducible⟩
      | inr rightReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := rightReducible
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              rightIH
                (.cons payloadReducible
                  (environmentReducible.weaken scrutineeExtension))
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            scrutineeExtension.trans branchExtension, resultStoreTyping,
            .caseRight scrutineeEvaluation branchEvaluation, resultReducible⟩
  | @newCell context elementType initializer initializerTyping payload
      initializerIH =>
      obtain ⟨initializedWorld, initializedStore, initialValue,
        initializerExtension, initializedStoreTyping, initializerEvaluation,
        initialValueReducible⟩ :=
          initializerIH environmentReducible storeTyping
      let resultWorld := initializedWorld ++ [elementType]
      let resultStore := (initializedStore.allocate initialValue).1
      have resultStoreTyping : StoreHasTypes resultWorld resultStore := by
        simpa [resultWorld, resultStore] using
          initializedStoreTyping.allocate payload initialValueReducible.hasType
      have freshLookup :
          resultWorld[(initializedStore.allocate initialValue).2]? =
            some elementType := by
        simp [resultWorld, ← initializedStoreTyping.length_eq]
      exact ⟨resultWorld, resultStore,
        .cellRef elementType (initializedStore.allocate initialValue).2,
        initializerExtension.trans ⟨[elementType], rfl⟩,
        resultStoreTyping, .newCell initializerEvaluation,
        by
          simp only [ReducibleValue]
          exact ⟨_, rfl, freshLookup⟩⟩
  | @loadCell context elementType reference referenceTyping payload referenceIH =>
      obtain ⟨referenceWorld, referenceStore, referenceValue,
        extension, referenceStoreTyping, referenceEvaluation,
        referenceReducible⟩ :=
          referenceIH environmentReducible storeTyping
      simp only [ReducibleValue] at referenceReducible
      obtain ⟨location, rfl, found⟩ := referenceReducible
      obtain ⟨storedValue, storedLookup, storedPayload, storedTyping⟩ :=
        referenceStoreTyping.lookup found
      exact ⟨referenceWorld, referenceStore, storedValue, extension,
        referenceStoreTyping, .loadCell referenceEvaluation storedLookup,
        storedPayload.reducible storedTyping⟩
  | @storeCell context elementType reference value referenceTyping valueTyping
      payload referenceIH valueIH =>
      obtain ⟨referenceWorld, referenceStore, referenceValue,
        referenceExtension, referenceStoreTyping, referenceEvaluation,
        referenceReducible⟩ :=
          referenceIH environmentReducible storeTyping
      simp only [ReducibleValue] at referenceReducible
      obtain ⟨location, rfl, found⟩ := referenceReducible
      obtain ⟨oldValue, oldLookup, _, _⟩ := referenceStoreTyping.lookup found
      obtain ⟨valueWorld, valueStore, newValue, valueExtension,
        valueStoreTyping, valueEvaluation, newValueReducible⟩ :=
          valueIH (environmentReducible.weaken referenceExtension)
            referenceStoreTyping
      have futureFound := valueExtension.lookup found
      obtain ⟨resultStore, written⟩ :=
        valueStoreTyping.write_exists (value := newValue) futureFound
      have resultStoreTyping :=
        valueStoreTyping.write futureFound newValueReducible.hasType written
      exact ⟨valueWorld, resultStore, .unit,
        referenceExtension.trans valueExtension, resultStoreTyping,
        .storeCell referenceEvaluation oldLookup valueEvaluation written,
        by simp only [ReducibleValue]⟩
  | unary operandTyping operandIH =>
      obtain ⟨resultWorld, resultStore, operandValue, extension,
        resultStoreTyping, operandEvaluation, operandReducible⟩ :=
          operandIH environmentReducible storeTyping
      obtain ⟨result, applied, _⟩ :=
        UnaryOp.apply_total_of_type _ operandValue operandReducible.hasType.type_eq
      exact ⟨resultWorld, resultStore, result, extension, resultStoreTyping,
        .unary operandEvaluation applied,
        unary_apply_result_reducible applied⟩
  | binary leftTyping rightTyping leftIH rightIH =>
      obtain ⟨rightWorld, rightStore, leftValue, leftExtension,
        rightStoreTyping, leftEvaluation, leftReducible⟩ :=
          leftIH environmentReducible storeTyping
      obtain ⟨resultWorld, resultStore, rightValue, rightExtension,
        resultStoreTyping, rightEvaluation, rightReducible⟩ :=
          rightIH (environmentReducible.weaken leftExtension) rightStoreTyping
      obtain ⟨result, applied, _⟩ :=
        BinaryOp.apply_total_of_types _ leftValue rightValue
          leftReducible.hasType.type_eq rightReducible.hasType.type_eq
      exact ⟨resultWorld, resultStore, result,
        leftExtension.trans rightExtension, resultStoreTyping,
        .binary leftEvaluation rightEvaluation applied,
        binary_apply_result_reducible applied⟩
  | letE boundTyping bodyTyping boundIH bodyIH =>
      obtain ⟨bodyWorld, bodyStore, boundValue, boundExtension,
        bodyStoreTyping, boundEvaluation, boundReducible⟩ :=
          boundIH environmentReducible storeTyping
      obtain ⟨resultWorld, resultStore, result, bodyExtension,
        resultStoreTyping, bodyEvaluation, resultReducible⟩ :=
          bodyIH
            (.cons boundReducible
              (environmentReducible.weaken boundExtension))
            bodyStoreTyping
      exact ⟨resultWorld, resultStore, result,
        boundExtension.trans bodyExtension, resultStoreTyping,
        .letE boundEvaluation bodyEvaluation, resultReducible⟩
  | ifE conditionTyping thenTyping elseTyping conditionIH thenIH elseIH =>
      obtain ⟨branchWorld, branchStore, conditionValue,
        conditionExtension, branchStoreTyping, conditionEvaluation,
        conditionReducible⟩ :=
          conditionIH environmentReducible storeTyping
      simp only [ReducibleValue] at conditionReducible
      obtain ⟨decision, rfl⟩ := conditionReducible
      cases decision with
      | false =>
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              elseIH (environmentReducible.weaken conditionExtension)
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            conditionExtension.trans branchExtension, resultStoreTyping,
            .ifFalse conditionEvaluation branchEvaluation, resultReducible⟩
      | true =>
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              thenIH (environmentReducible.weaken conditionExtension)
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            conditionExtension.trans branchExtension, resultStoreTyping,
            .ifTrue conditionEvaluation branchEvaluation, resultReducible⟩

theorem RuntimeValueHasType.reducible
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type) :
    ReducibleValue world type value := by
  induction typing using RuntimeValueHasType.rec
      (motive_2 := fun environment context _ =>
        ReducibleEnvironment world environment context) with
  | unit => simp only [ReducibleValue]
  | bool =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | word =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | pair _ _ leftIH rightIH =>
      simp only [ReducibleValue]
      exact ⟨_, _, rfl, leftIH, rightIH⟩
  | inLeft _ payloadIH =>
      simp only [ReducibleValue]
      exact .inl ⟨_, rfl, payloadIH⟩
  | inRight _ payloadIH =>
      simp only [ReducibleValue]
      exact .inr ⟨_, rfl, payloadIH⟩
  | @closure parameterType resultType body environment context
      environmentTyping bodyTyping environmentIH =>
      simp only [ReducibleValue]
      exact ⟨body, environment, context, rfl,
        environmentTyping, bodyTyping,
        fun futureExtension futureStoreTyping argumentReducible =>
          reducibility_fundamental bodyTyping
            (.cons argumentReducible
              (environmentIH.weaken futureExtension))
            futureStoreTyping⟩
  | cellRef found =>
      simp only [ReducibleValue]
      exact ⟨_, rfl, found⟩
  | nil => exact .nil
  | cons _ _ valueIH environmentIH => exact .cons valueIH environmentIH

theorem RuntimeEnvironmentHasTypes.reducible
    {world : StoreTyping} {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes world environment context) :
    ReducibleEnvironment world environment context := by
  cases typing with
  | nil => exact .nil
  | cons valueTyping environmentTyping =>
      exact .cons valueTyping.reducible environmentTyping.reducible
termination_by environment

theorem reducible_environment_evaluates
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentReducible : ReducibleEnvironment world environment context)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      RuntimeValueHasType finalWorld value type := by
  obtain ⟨finalWorld, finalStore, value, extension,
    finalStoreTyping, evaluation, valueReducible⟩ :=
      reducibility_fundamental typing environmentReducible storeTyping
  exact ⟨finalWorld, finalStore, value, extension, finalStoreTyping,
    evaluation, valueReducible.runtimeHasType⟩

theorem well_typed_evaluates
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentTyping : RuntimeEnvironmentHasTypes world environment context)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      RuntimeValueHasType finalWorld value type :=
  reducible_environment_evaluates typing environmentTyping.reducible storeTyping

theorem closed_well_typed_evaluates
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      Evaluates [] [] expr value finalStore ∧
      RuntimeValueHasType finalWorld value type := by
  obtain ⟨finalWorld, finalStore, value, _, finalStoreTyping,
    evaluation, valueTyping⟩ :=
      well_typed_evaluates typing .nil .nil
  exact ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩

theorem closed_well_typed_runStateful_completes
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing
  obtain ⟨fuel, result⟩ := evaluation_runStateful_complete evaluation
  exact ⟨fuel, finalWorld, finalStore, value, result,
    finalStoreTyping, valueTyping⟩

theorem closed_well_typed_run_stateful_completes
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type :=
  closed_well_typed_runStateful_completes typing

theorem closed_well_typed_runStateful_has_sufficient_fuel
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, finalWorld, finalStore, value,
    finalStoreTyping, valueTyping, completes⟩

theorem closed_well_typed_run_stateful_has_sufficient_fuel
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore :=
  closed_well_typed_runStateful_has_sufficient_fuel typing

theorem closed_well_typed_run_completes
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ fuel value,
      run fuel (State.initial expr) = .done value ∧
      ValueHasType value type := by
  obtain ⟨fuel, finalWorld, finalStore, value, result, _, valueTyping⟩ :=
    closed_well_typed_runStateful_completes typing
  exact ⟨fuel, value,
    by simp [run, result, StatefulRunResult.erase], valueTyping.erase⟩

theorem closed_well_typed_run_has_sufficient_fuel
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ required value,
      ValueHasType value type ∧
      ∀ fuel, required ≤ fuel →
        run fuel (State.initial expr) = .done value := by
  obtain ⟨required, finalWorld, finalStore, value, _, valueTyping,
    completes⟩ := closed_well_typed_runStateful_has_sufficient_fuel typing
  exact ⟨required, value, valueTyping.erase, fun fuel enough => by
    simp [run, completes fuel enough, StatefulRunResult.erase]⟩

/-! ## Typed CEK states -/

inductive FrameHasType
    (world : StoreTyping) : Frame → Ty → Ty → Prop where
  | unaryApply {op : UnaryOp} :
      FrameHasType world (.unaryApply op) op.operandType op.resultType
  | binaryRight
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {context : Context} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType context right op.rightType →
      FrameHasType world (.binaryRight op right environment)
        op.leftType op.resultType
  | binaryApply {op : BinaryOp} {leftValue : Value} :
      RuntimeValueHasType world leftValue op.leftType →
      FrameHasType world (.binaryApply op leftValue)
        op.rightType op.resultType
  | pairRight
      {right : Expr} {environment : Environment} {context : Context}
      {leftType rightType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType context right rightType →
      FrameHasType world (.pairRight right environment)
        leftType (.product leftType rightType)
  | pairApply
      {leftValue : Value} {leftType rightType : Ty} :
      RuntimeValueHasType world leftValue leftType →
      FrameHasType world (.pairApply leftValue)
        rightType (.product leftType rightType)
  | firstApply {leftType rightType : Ty} :
      FrameHasType world .firstApply (.product leftType rightType) leftType
  | secondApply {leftType rightType : Ty} :
      FrameHasType world .secondApply (.product leftType rightType) rightType
  | inLeftApply {leftType rightType : Ty} :
      FrameHasType world (.inLeftApply rightType)
        leftType (.sum leftType rightType)
  | inRightApply {leftType rightType : Ty} :
      FrameHasType world (.inRightApply leftType)
        rightType (.sum leftType rightType)
  | caseBranches
      {leftBranch rightBranch : Expr} {environment : Environment}
      {context : Context} {leftType rightType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType (leftType :: context) leftBranch resultType →
      HasType (rightType :: context) rightBranch resultType →
      FrameHasType world
        (.caseBranches leftBranch rightBranch environment)
        (.sum leftType rightType) resultType
  | newCellApply {elementType : Ty} :
      CellPayload elementType →
      FrameHasType world (.newCellApply elementType)
        elementType (.cell elementType)
  | loadCellApply {elementType : Ty} :
      CellPayload elementType →
      FrameHasType world .loadCellApply (.cell elementType) elementType
  | storeCellValue
      {valueExpr : Expr} {environment : Environment} {context : Context}
      {elementType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType context valueExpr elementType →
      CellPayload elementType →
      FrameHasType world (.storeCellValue valueExpr environment)
        (.cell elementType) .unit
  | storeCellApply {elementType : Ty} {location : Location} :
      world[location]? = some elementType →
      CellPayload elementType →
      FrameHasType world (.storeCellApply elementType location)
        elementType .unit
  | applyArgument
      {argument : Expr} {environment : Environment} {context : Context}
      {parameterType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType context argument parameterType →
      FrameHasType world (.applyArgument argument environment)
        (.function parameterType resultType) resultType
  | applyClosure
      {parameterType resultType : Ty} {body : Expr}
      {environment : Environment} {context : Context} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType (parameterType :: context) body resultType →
      FrameHasType world
        (.applyClosure parameterType resultType body environment)
        parameterType resultType
  | letBody
      {body : Expr} {environment : Environment} {context : Context}
      {inputType outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType (inputType :: context) body outputType →
      FrameHasType world (.letBody body environment) inputType outputType
  | ifBranches
      {thenBranch elseBranch : Expr} {environment : Environment}
      {context : Context} {outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context →
      HasType context thenBranch outputType →
      HasType context elseBranch outputType →
      FrameHasType world
        (.ifBranches thenBranch elseBranch environment) .bool outputType

inductive ContinuationHasType
    (world : StoreTyping) : List Frame → Ty → Ty → Prop where
  | nil {type : Ty} : ContinuationHasType world [] type type
  | cons
      {frame : Frame} {continuation : List Frame}
      {inputType middleType outputType : Ty} :
      FrameHasType world frame inputType middleType →
      ContinuationHasType world continuation middleType outputType →
      ContinuationHasType world (frame :: continuation) inputType outputType

theorem FrameHasType.weaken
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {frame : Frame} {inputType outputType : Ty}
    (typing : FrameHasType initial frame inputType outputType) :
    FrameHasType future frame inputType outputType := by
  cases typing with
  | unaryApply => exact .unaryApply
  | binaryRight environmentTyping rightTyping =>
      exact .binaryRight (environmentTyping.weaken extension) rightTyping
  | binaryApply leftTyping =>
      exact .binaryApply (leftTyping.weaken extension)
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
  | newCellApply payload => exact .newCellApply payload
  | loadCellApply payload => exact .loadCellApply payload
  | storeCellValue environmentTyping valueTyping payload =>
      exact .storeCellValue (environmentTyping.weaken extension)
        valueTyping payload
  | storeCellApply found payload =>
      exact .storeCellApply (extension.lookup found) payload
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
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {continuation : List Frame} {inputType outputType : Ty}
    (typing : ContinuationHasType initial continuation inputType outputType) :
    ContinuationHasType future continuation inputType outputType := by
  induction typing with
  | nil => exact .nil
  | cons frameTyping _ tailIH =>
      exact .cons (frameTyping.weaken extension) tailIH

inductive StateHasType : State → Ty → Prop where
  | eval
      {world : StoreTyping} {expr : Expr} {environment : Environment}
      {context : Context} {continuation : List Frame} {store : Store}
      {controlType resultType : Ty} :
      StoreHasTypes world store →
      RuntimeEnvironmentHasTypes world environment context →
      HasType context expr controlType →
      ContinuationHasType world continuation controlType resultType →
      StateHasType
        ⟨.eval expr environment, continuation, store⟩ resultType
  | ret
      {world : StoreTyping} {value : Value} {continuation : List Frame}
      {store : Store} {controlType resultType : Ty} :
      StoreHasTypes world store →
      RuntimeValueHasType world value controlType →
      ContinuationHasType world continuation controlType resultType →
      StateHasType ⟨.ret value, continuation, store⟩ resultType

theorem transition_preserves_state_type
    {state next : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType)
    (transition : Transition state next) :
    StateHasType next resultType := by
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
          | inLeft payloadTyping =>
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
          | inRight payloadTyping =>
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
          | newCell initializerTyping payload =>
              exact .eval storeTyping environmentTyping initializerTyping
                (.cons (.newCellApply payload) continuationTyping)
  | @applyNewCell elementType initialValue continuation store =>
      cases stateTyping with
      | @ret world _ _ _ _ _ storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | @newCellApply elementType payload =>
                  let futureWorld := world ++ [elementType]
                  have extension : WorldExtends world futureWorld :=
                    ⟨[elementType], rfl⟩
                  have futureStoreTyping :
                      StoreHasTypes futureWorld (store.allocate initialValue).1 := by
                    simpa [futureWorld] using
                      storeTyping.allocate payload valueTyping.erase
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
          | loadCell referenceTyping payload =>
              exact .eval storeTyping environmentTyping referenceTyping
                (.cons (.loadCellApply payload) continuationTyping)
  | applyLoadCell loaded =>
      cases stateTyping with
      | ret storeTyping cellTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | loadCellApply _ =>
                  cases cellTyping with
                  | cellRef found =>
                      obtain ⟨stored, storedRead, storedPayload, storedTyping⟩ :=
                        storeTyping.lookup found
                      rw [loaded] at storedRead
                      cases storedRead
                      exact .ret storeTyping
                        (storedPayload.runtimeValueHasType storedTyping)
                        restTyping
  | enterStoreCell =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | storeCell referenceTyping valueTyping payload =>
              exact .eval storeTyping environmentTyping referenceTyping
                (.cons
                  (.storeCellValue environmentTyping valueTyping payload)
                  continuationTyping)
  | beginStoreCellValue _ =>
      cases stateTyping with
      | ret storeTyping cellTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | storeCellValue environmentTyping valueTyping payload =>
                  cases cellTyping with
                  | cellRef found =>
                      exact .eval storeTyping environmentTyping valueTyping
                        (.cons (.storeCellApply found payload) restTyping)
  | applyStoreCell written =>
      cases stateTyping with
      | ret storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | storeCellApply found _ =>
                  exact .ret
                    (storeTyping.write found valueTyping.erase written)
                    .unit restTyping
  | lambda =>
      cases stateTyping with
      | eval storeTyping environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | lambda bodyTyping =>
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
                    (unary_apply_result_has_runtime_type applied) restTyping
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
                    (binary_apply_result_has_runtime_type applied) restTyping
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
    {state : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType) :
    (∃ value store, state = State.final value store) ∨
      ∃ next, Transition state next := by
  cases stateTyping with
  | eval storeTyping environmentTyping exprTyping continuationTyping =>
      cases exprTyping with
      | unit => exact .inr ⟨_, .unit⟩
      | bool => exact .inr ⟨_, .bool⟩
      | word => exact .inr ⟨_, .word⟩
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
      | unary => exact .inr ⟨_, .enterUnary⟩
      | binary => exact .inr ⟨_, .enterBinary⟩
      | letE => exact .inr ⟨_, .enterLet⟩
      | ifE => exact .inr ⟨_, .enterIf⟩
  | @ret world value continuation store controlType resultType
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
          | newCellApply _ => exact .inr ⟨_, .applyNewCell⟩
          | loadCellApply _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨loaded, read, _, _⟩ := storeTyping.lookup found
                  exact .inr ⟨_, .applyLoadCell read⟩
          | storeCellValue _ _ _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨oldValue, read, _, _⟩ := storeTyping.lookup found
                  exact .inr ⟨_, .beginStoreCellValue read⟩
          | storeCellApply found _ =>
              obtain ⟨updatedStore, written⟩ :=
                storeTyping.write_exists (value := value) found
              exact .inr ⟨_, .applyStoreCell written⟩
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
    {steps : Nat} {start finish : State} {resultType : Ty}
    (path : Steps steps start finish)
    (startTyping : StateHasType start resultType) :
    StateHasType finish resultType := by
  induction path with
  | refl => exact startTyping
  | cons transition tail tailIH =>
      exact tailIH (transition_preserves_state_type startTyping transition)

theorem well_typed_state_never_faults
    {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
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
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    StateHasType (State.initial expr) type :=
  .eval .nil .nil typing .nil

theorem well_typed_runStateful_never_faults
    {fuel : Nat} {state faultState : State}
    {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
    runStateful fuel state ≠ .fault error faultState := by
  intro faulted
  obtain ⟨steps, _, path, terminal⟩ := runStateful_fault_sound faulted
  exact well_typed_state_never_faults
    (path.preserve_state_type stateTyping) terminal

theorem well_typed_run_stateful_never_faults
    {fuel : Nat} {state faultState : State}
    {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
    runStateful fuel state ≠ .fault error faultState :=
  well_typed_runStateful_never_faults stateTyping

theorem well_typed_runStateful_preserves_result_type
    {fuel : Nat} {state : State} {resultType : Ty}
    {value : Value} {finalStore : Store}
    (stateTyping : StateHasType state resultType)
    (result : runStateful fuel state = .done value finalStore) :
    ∃ finalWorld,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value resultType := by
  obtain ⟨steps, _, path⟩ := runStateful_sound result
  have finalTyping := path.preserve_state_type stateTyping
  cases finalTyping with
  | ret storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact ⟨_, storeTyping, valueTyping⟩

theorem well_typed_run_stateful_preserves_result_type
    {fuel : Nat} {state : State} {resultType : Ty}
    {value : Value} {finalStore : Store}
    (stateTyping : StateHasType state resultType)
    (result : runStateful fuel state = .done value finalStore) :
    ∃ finalWorld,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value resultType :=
  well_typed_runStateful_preserves_result_type stateTyping result

theorem well_typed_run_never_faults
    {fuel : Nat} {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
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
    {fuel : Nat} {state : State} {resultType : Ty} {value : Value}
    (stateTyping : StateHasType state resultType)
    (result : run fuel state = .done value) :
    ValueHasType value resultType := by
  obtain ⟨finalStore, steps, _, path⟩ := run_sound result
  have finalTyping := path.preserve_state_type stateTyping
  cases finalTyping with
  | ret storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact valueTyping.erase

theorem closed_well_typed_runStateful_never_faults
    {fuel : Nat} {expr : Expr} {type : Ty}
    {error : MachineFault} {faultState : State}
    (typing : HasType [] expr type) :
    runStateful fuel (State.initial expr) ≠ .fault error faultState :=
  well_typed_runStateful_never_faults (initial_state_has_type typing)

theorem closed_well_typed_run_stateful_never_faults
    {fuel : Nat} {expr : Expr} {type : Ty}
    {error : MachineFault} {faultState : State}
    (typing : HasType [] expr type) :
    runStateful fuel (State.initial expr) ≠ .fault error faultState :=
  closed_well_typed_runStateful_never_faults typing

theorem closed_well_typed_run_never_faults
    {fuel : Nat} {expr : Expr} {type : Ty} {error : MachineFault}
    (typing : HasType [] expr type) :
    run fuel (State.initial expr) ≠ .fault error :=
  well_typed_run_never_faults (initial_state_has_type typing)

theorem Program.checked_runStateful_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value} {finalStore : Store}
    (checked : program.check = true)
    (result : program.runStateful fuel = .done value finalStore) :
    ∃ finalWorld,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType := by
  exact well_typed_runStateful_preserves_result_type
    (initial_state_has_type (Program.check_sound checked)) result

theorem Program.checked_run_stateful_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value} {finalStore : Store}
    (checked : program.check = true)
    (result : program.runStateful fuel = .done value finalStore) :
    ∃ finalWorld,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType :=
  Program.checked_runStateful_preserves_result_type checked result

theorem Program.checked_run_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value}
    (checked : program.check = true)
    (result : program.run fuel = .done value) :
    ValueHasType value program.resultType :=
  well_typed_run_preserves_result_type
    (initial_state_has_type (Program.check_sound checked)) result

theorem Program.checked_runStateful_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType := by
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_completes (Program.check_sound checked)

theorem Program.checked_run_stateful_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType :=
  Program.checked_runStateful_completes checked

theorem Program.checked_run_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel value,
      program.run fuel = .done value ∧
      ValueHasType value program.resultType := by
  simpa [Program.run] using
    closed_well_typed_run_completes (Program.check_sound checked)

theorem Program.checked_runStateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore := by
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_has_sufficient_fuel
      (Program.check_sound checked)

theorem Program.checked_run_stateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore :=
  Program.checked_runStateful_has_sufficient_fuel checked

theorem Program.checked_run_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required value,
      ValueHasType value program.resultType ∧
      ∀ fuel, required ≤ fuel →
        program.run fuel = .done value := by
  simpa [Program.run] using
    closed_well_typed_run_has_sufficient_fuel (Program.check_sound checked)

theorem Program.checked_runStateful_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    {faultState : State}
    (checked : program.check = true) :
    program.runStateful fuel ≠ .fault error faultState :=
  closed_well_typed_runStateful_never_faults (Program.check_sound checked)

theorem Program.checked_run_stateful_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    {faultState : State}
    (checked : program.check = true) :
    program.runStateful fuel ≠ .fault error faultState :=
  Program.checked_runStateful_never_faults checked

theorem Program.checked_run_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    (checked : program.check = true) :
    program.run fuel ≠ .fault error :=
  closed_well_typed_run_never_faults (Program.check_sound checked)

end Solcore.Core
