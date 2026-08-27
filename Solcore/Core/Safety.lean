import Solcore.Core.Correspondence

set_option autoImplicit false

namespace Solcore.Core

/-! ## Structural value typing -/

mutual

  inductive ValueHasType :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} : ValueHasType .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        ValueHasType (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        ValueHasType (.word value) .word definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        ValueHasType left leftType definitions →
        ValueHasType right rightType definitions →
        ValueHasType (.pair left right) (.product leftType rightType) definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload leftType definitions →
        ValueHasType (.inLeft rightType payload) (.sum leftType rightType)
          definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload rightType definitions →
        ValueHasType (.inRight leftType payload) (.sum leftType rightType)
          definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        EnvironmentHasTypes environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        ValueHasType
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
          definitions
    | cellRef
        {definitions : DataEnvironment} {elementType : Ty} {location : Location} :
        ValueHasType (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        ValueHasType payload payloadType definitions →
        ValueHasType (.constructed constructor payload)
          (.namedData constructor.owner) definitions

  inductive EnvironmentHasTypes :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} : EnvironmentHasTypes [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        ValueHasType value type definitions →
        EnvironmentHasTypes environment context definitions →
        EnvironmentHasTypes (value :: environment) (type :: context) definitions

end

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
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef
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
  | unit | bool | word | closure | cellRef | constructed => rfl
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
      (world : StoreTyping) :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} :
        RuntimeValueHasType world .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        RuntimeValueHasType world (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        RuntimeValueHasType world (.word value) .word definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world left leftType definitions →
        RuntimeValueHasType world right rightType definitions →
        RuntimeValueHasType world (.pair left right) (.product leftType rightType)
          definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload leftType definitions →
        RuntimeValueHasType world
          (.inLeft rightType payload) (.sum leftType rightType) definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload rightType definitions →
        RuntimeValueHasType world
          (.inRight leftType payload) (.sum leftType rightType) definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        RuntimeEnvironmentHasTypes world environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        RuntimeValueHasType world
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
          definitions
    | cellRef
        {definitions : DataEnvironment}
        {elementType : Ty} {location : Location} :
        world[location]? = some elementType →
        RuntimeValueHasType world
          (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        RuntimeValueHasType world payload payloadType definitions →
        RuntimeValueHasType world (.constructed constructor payload)
          (.namedData constructor.owner) definitions

  inductive RuntimeEnvironmentHasTypes
      (world : StoreTyping) :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} :
        RuntimeEnvironmentHasTypes world [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        RuntimeValueHasType world value type definitions →
        RuntimeEnvironmentHasTypes world environment context definitions →
        RuntimeEnvironmentHasTypes world
          (value :: environment) (type :: context) definitions

end

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
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef
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
  | unit | bool | word | var | pair | first | second | lambda | apply
  | inLeft | inRight | caseE | newCell | loadCell | storeCell | construct
  | matchData | unary | binary | letE | ifE =>
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
  | unit | bool | word | var | pair | first | second | lambda | apply
  | inLeft | inRight | caseE | newCell | loadCell | storeCell | construct
  | matchData | unary | binary | letE | ifE =>
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

/-! ## Preservation for the state-threaded evaluator -/

theorem evaluation_preserves_type
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store}
    {expr : Expr} {value : Value} {type : Ty} {world : StoreTyping}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (typing : HasType context expr type definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    ∃ finalWorld,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
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
      | newCell initializerTyping payload =>
          obtain ⟨initializedWorld, initializerExtension,
            initializedStoreTyping, initialValueTyping⟩ :=
              initializerIH initializerTyping environmentTyping storeTyping
          let resultWorld := initializedWorld ++ [elementType]
          have resultStoreTyping :
              StoreHasTypes resultWorld
                (initializedStore.allocate initialValue).1 := by
            simpa [resultWorld] using
              initializedStoreTyping.allocate payload
                (payload.valueHasType_rebase initialValueTyping.erase)
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
                payload.runtimeValueHasType
                  (definitions := definitions) storedTyping⟩
  | storeCell _ _ _ written referenceIH valueIH =>
      cases typing with
      | storeCell referenceTyping valueTyping payload =>
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
                valueStoreTyping.write futureFound
                  (by
                    apply payload.valueHasType_rebase
                    exact newValueTyping.erase)
                  written
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
  | ternary => cases typing
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
    (world : StoreTyping)
    (type : Ty)
    (value : Value)
    (definitions : DataEnvironment := []) : Prop :=
  match type with
  | .unit => value = .unit
  | .bool => ∃ decision, value = .bool decision
  | .word => ∃ word, value = .word word
  | .product leftType rightType =>
      ∃ left right,
        value = .pair left right ∧
        ReducibleValue world leftType left definitions ∧
        ReducibleValue world rightType right definitions
  | .sum leftType rightType =>
      (∃ payload,
        value = .inLeft rightType payload ∧
        ReducibleValue world leftType payload definitions) ∨
      (∃ payload,
        value = .inRight leftType payload ∧
        ReducibleValue world rightType payload definitions)
  | .function parameterType resultType =>
      ∃ body environment context,
        value = .closure parameterType resultType body environment ∧
        RuntimeEnvironmentHasTypes world environment context definitions ∧
        HasType (parameterType :: context) body resultType definitions ∧
        ∀ {futureWorld : StoreTyping} {futureStore : Store}
            {argument : Value},
          WorldExtends world futureWorld →
          StoreHasTypes futureWorld futureStore →
          ReducibleValue futureWorld parameterType argument definitions →
          ∃ finalWorld finalStore result,
            WorldExtends futureWorld finalWorld ∧
            StoreHasTypes finalWorld finalStore ∧
            Evaluates (argument :: environment) futureStore body result finalStore ∧
            ReducibleValue finalWorld resultType result definitions
  | .cell elementType =>
      ∃ location,
        value = .cellRef elementType location ∧
        world[location]? = some elementType
  | .namedData dataType =>
      RuntimeValueHasType world value (.namedData dataType) definitions

inductive ReducibleEnvironment
    (world : StoreTyping) :
    Environment → Context → (definitions : DataEnvironment := []) → Prop where
  | nil {definitions : DataEnvironment} :
      ReducibleEnvironment world [] [] definitions
  | cons
      {definitions : DataEnvironment}
      {value : Value} {type : Ty}
      {environment : Environment} {context : Context} :
      ReducibleValue world type value definitions →
      ReducibleEnvironment world environment context definitions →
      ReducibleEnvironment world (value :: environment) (type :: context)
        definitions

theorem ReducibleEnvironment.lookup
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context definitions)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧
        ReducibleValue world type value definitions := by
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
    {definitions : DataEnvironment}
    {world : StoreTyping} {type : Ty} {value : Value}
    (reducible : ReducibleValue world type value definitions) :
    RuntimeValueHasType world value type definitions := by
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
  | namedData dataType =>
      exact reducible

theorem ReducibleValue.hasType
    {definitions : DataEnvironment}
    {world : StoreTyping} {type : Ty} {value : Value}
    (reducible : ReducibleValue world type value definitions) :
    ValueHasType value type definitions :=
  reducible.runtimeHasType.erase

theorem ReducibleEnvironment.runtimeHasTypes
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context definitions) :
    RuntimeEnvironmentHasTypes world environment context definitions := by
  induction reducible with
  | nil => exact .nil
  | cons headReducible _ tailIH =>
      exact .cons headReducible.runtimeHasType tailIH

theorem ReducibleEnvironment.hasTypes
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment world environment context definitions) :
    EnvironmentHasTypes environment context definitions :=
  reducible.runtimeHasTypes.erase

theorem ReducibleValue.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {type : Ty} {value : Value}
    (reducible : ReducibleValue initial type value definitions) :
    ReducibleValue future type value definitions := by
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
  | namedData dataType =>
      exact RuntimeValueHasType.weaken extension reducible

theorem ReducibleEnvironment.weaken
    {definitions : DataEnvironment}
    {initial future : StoreTyping}
    (extension : WorldExtends initial future)
    {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment initial environment context definitions) :
    ReducibleEnvironment future environment context definitions := by
  induction reducible with
  | nil => exact .nil
  | cons headReducible _ tailIH =>
      exact .cons (headReducible.weaken extension) tailIH

theorem CellPayload.reducible
    {elementType : Ty}
    (payload : CellPayload elementType)
    {world : StoreTyping} {value : Value}
    (typing : ValueHasType value elementType)
    (definitions : DataEnvironment := []) :
    ReducibleValue world elementType value definitions := by
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

theorem ConstructorPayload.reducible
    {definitions : DataEnvironment} {type : Ty}
    (payload : ConstructorPayload definitions type)
    {world : StoreTyping} {value : Value}
    (typing : RuntimeValueHasType world value type definitions) :
    ReducibleValue world type value definitions := by
  induction payload generalizing value with
  | unit => cases typing; simp only [ReducibleValue]
  | bool =>
      cases typing with
      | bool => simp only [ReducibleValue]; exact ⟨_, rfl⟩
  | word =>
      cases typing with
      | word => simp only [ReducibleValue]; exact ⟨_, rfl⟩
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
  | cell cellPayload =>
      cases typing with
      | cellRef found =>
          simp only [ReducibleValue]
          exact ⟨_, rfl, found⟩
  | namedData lookup =>
      exact typing

theorem unary_apply_result_reducible
    {world : StoreTyping} {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result)
    (definitions : DataEnvironment := []) :
    ReducibleValue world op.resultType result definitions := by
  apply CellPayload.reducible
    (definitions := definitions)
    (typing := unary_apply_result_has_type applied (definitions := []))
  cases op <;> constructor

theorem binary_apply_result_reducible
    {world : StoreTyping} {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result)
    (definitions : DataEnvironment := []) :
    ReducibleValue world op.resultType result definitions := by
  apply CellPayload.reducible
    (definitions := definitions)
    (typing := binary_apply_result_has_type applied (definitions := []))
  cases op <;> constructor

theorem reducibility_fundamental
    {definitions : DataEnvironment}
    {context : Context} {expr : Expr} {type : Ty}
    (definitionsWellFormed : definitions.WellFormed)
    (typing : HasType context expr type definitions)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentReducible :
      ReducibleEnvironment world environment context definitions)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      ReducibleValue finalWorld type value definitions := by
  induction typing using HasType.rec
      (motive_2 := fun branchContext branchResult payloadTypes branches
          branchDefinitions _ =>
        branchDefinitions.WellFormed →
        ∀ {world : StoreTyping} {environment : Environment} {store : Store}
            {index : Nat} {payloadType : Ty} {payloadValue : Value},
          ReducibleEnvironment world environment branchContext
            branchDefinitions →
          StoreHasTypes world store →
          payloadTypes[index]? = some payloadType →
          ReducibleValue world payloadType payloadValue branchDefinitions →
          ∃ branch finalWorld finalStore result,
            branches[index]? = some branch ∧
            WorldExtends world finalWorld ∧
            StoreHasTypes finalWorld finalStore ∧
            Evaluates (payloadValue :: environment) store branch result finalStore ∧
            ReducibleValue finalWorld branchResult result branchDefinitions)
      generalizing world environment store with
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
          leftIH definitionsWellFormed environmentReducible storeTyping
      obtain ⟨rightWorld, rightStore, rightValue, rightExtension,
        rightStoreTyping, rightEvaluation, rightReducible⟩ :=
          rightIH definitionsWellFormed
            (environmentReducible.weaken leftExtension) leftStoreTyping
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
          operandIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl, leftReducible, _⟩ := operandReducible
      exact ⟨resultWorld, resultStore, leftValue, extension,
        resultStoreTyping, .first operandEvaluation, leftReducible⟩
  | second operandTyping operandIH =>
      obtain ⟨resultWorld, resultStore, operandValue, extension,
        resultStoreTyping, operandEvaluation, operandReducible⟩ :=
          operandIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl, _, rightReducible⟩ := operandReducible
      exact ⟨resultWorld, resultStore, rightValue, extension,
        resultStoreTyping, .second operandEvaluation, rightReducible⟩
  | @lambda context _ parameterType resultType body _ _ bodyTyping bodyIH =>
      refine ⟨world, store,
        .closure parameterType resultType body environment,
        .refl world, storeTyping, .lambda, ?_⟩
      simp only [ReducibleValue]
      exact ⟨body, environment, context, rfl,
        environmentReducible.runtimeHasTypes, bodyTyping,
        fun futureExtension futureStoreTyping argumentReducible =>
          bodyIH
            definitionsWellFormed
            (.cons argumentReducible
              (environmentReducible.weaken futureExtension))
            futureStoreTyping⟩
  | @apply context _ function argument parameterType resultType
      functionTyping argumentTyping functionIH argumentIH =>
      obtain ⟨functionWorld, functionStore, functionValue,
        functionExtension, functionStoreTyping, functionEvaluation,
        functionReducible⟩ :=
          functionIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at functionReducible
      obtain ⟨body, capturedEnvironment, capturedContext, rfl,
        capturedTyping, bodyTyping, callable⟩ := functionReducible
      obtain ⟨argumentWorld, argumentStore, argumentValue,
        argumentExtension, argumentStoreTyping, argumentEvaluation,
        argumentReducible⟩ :=
          argumentIH definitionsWellFormed
            (environmentReducible.weaken functionExtension)
            functionStoreTyping
      obtain ⟨resultWorld, resultStore, result, bodyExtension,
        resultStoreTyping, bodyEvaluation, resultReducible⟩ :=
          callable argumentExtension argumentStoreTyping argumentReducible
      exact ⟨resultWorld, resultStore, result,
        functionExtension.trans (argumentExtension.trans bodyExtension),
        resultStoreTyping,
        .apply functionEvaluation argumentEvaluation bodyEvaluation,
        resultReducible⟩
  | @inLeft context _ rightType leftType payload _ payloadTyping payloadIH =>
      obtain ⟨resultWorld, resultStore, payloadValue, extension,
        resultStoreTyping, payloadEvaluation, payloadReducible⟩ :=
          payloadIH definitionsWellFormed environmentReducible storeTyping
      exact ⟨resultWorld, resultStore, .inLeft rightType payloadValue,
        extension, resultStoreTyping, .inLeft payloadEvaluation,
        by
          simp only [ReducibleValue]
          exact .inl ⟨payloadValue, rfl, payloadReducible⟩⟩
  | @inRight context _ leftType rightType payload _ payloadTyping payloadIH =>
      obtain ⟨resultWorld, resultStore, payloadValue, extension,
        resultStoreTyping, payloadEvaluation, payloadReducible⟩ :=
          payloadIH definitionsWellFormed environmentReducible storeTyping
      exact ⟨resultWorld, resultStore, .inRight leftType payloadValue,
        extension, resultStoreTyping, .inRight payloadEvaluation,
        by
          simp only [ReducibleValue]
          exact .inr ⟨payloadValue, rfl, payloadReducible⟩⟩
  | @caseE context _ scrutinee leftBranch rightBranch
      leftType rightType resultType
      scrutineeTyping leftTyping rightTyping
      scrutineeIH leftIH rightIH =>
      obtain ⟨branchWorld, branchStore, scrutineeValue,
        scrutineeExtension, branchStoreTyping, scrutineeEvaluation,
        scrutineeReducible⟩ :=
          scrutineeIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at scrutineeReducible
      cases scrutineeReducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              leftIH
                definitionsWellFormed
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
                definitionsWellFormed
                (.cons payloadReducible
                  (environmentReducible.weaken scrutineeExtension))
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            scrutineeExtension.trans branchExtension, resultStoreTyping,
            .caseRight scrutineeEvaluation branchEvaluation, resultReducible⟩
  | @newCell context _ elementType initializer initializerTyping payload
      initializerIH =>
      obtain ⟨initializedWorld, initializedStore, initialValue,
        initializerExtension, initializedStoreTyping, initializerEvaluation,
        initialValueReducible⟩ :=
          initializerIH definitionsWellFormed environmentReducible storeTyping
      let resultWorld := initializedWorld ++ [elementType]
      let resultStore := (initializedStore.allocate initialValue).1
      have resultStoreTyping : StoreHasTypes resultWorld resultStore := by
        simpa [resultWorld, resultStore] using
          initializedStoreTyping.allocate payload
            (payload.valueHasType_rebase initialValueReducible.hasType)
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
  | @loadCell context _ elementType reference referenceTyping payload referenceIH =>
      obtain ⟨referenceWorld, referenceStore, referenceValue,
        extension, referenceStoreTyping, referenceEvaluation,
        referenceReducible⟩ :=
          referenceIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at referenceReducible
      obtain ⟨location, rfl, found⟩ := referenceReducible
      obtain ⟨storedValue, storedLookup, storedPayload, storedTyping⟩ :=
        referenceStoreTyping.lookup found
      exact ⟨referenceWorld, referenceStore, storedValue, extension,
        referenceStoreTyping, .loadCell referenceEvaluation storedLookup,
        storedPayload.reducible (definitions := _) storedTyping⟩
  | @storeCell context _ elementType reference value referenceTyping valueTyping
      payload referenceIH valueIH =>
      obtain ⟨referenceWorld, referenceStore, referenceValue,
        referenceExtension, referenceStoreTyping, referenceEvaluation,
        referenceReducible⟩ :=
          referenceIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at referenceReducible
      obtain ⟨location, rfl, found⟩ := referenceReducible
      obtain ⟨oldValue, oldLookup, _, _⟩ := referenceStoreTyping.lookup found
      obtain ⟨valueWorld, valueStore, newValue, valueExtension,
        valueStoreTyping, valueEvaluation, newValueReducible⟩ :=
          valueIH definitionsWellFormed
            (environmentReducible.weaken referenceExtension)
            referenceStoreTyping
      have futureFound := valueExtension.lookup found
      obtain ⟨resultStore, written⟩ :=
        valueStoreTyping.write_exists (value := newValue) futureFound
      have resultStoreTyping :=
        valueStoreTyping.write futureFound
          (payload.valueHasType_rebase newValueReducible.hasType) written
      exact ⟨valueWorld, resultStore, .unit,
        referenceExtension.trans valueExtension, resultStoreTyping,
        .storeCell referenceEvaluation oldLookup valueEvaluation written,
        by simp only [ReducibleValue]⟩
  | construct constructorLookup payloadTyping payloadIH =>
      obtain ⟨resultWorld, resultStore, payloadValue, extension,
        resultStoreTyping, payloadEvaluation, payloadReducible⟩ :=
          payloadIH definitionsWellFormed environmentReducible storeTyping
      exact ⟨resultWorld, resultStore, .constructed _ payloadValue,
        extension, resultStoreTyping, .construct payloadEvaluation,
        .constructed constructorLookup payloadReducible.runtimeHasType⟩
  | matchData definitionLookup _ scrutineeTyping branchesTyping
      scrutineeIH branchesIH =>
      obtain ⟨branchWorld, branchStore, scrutineeValue,
        scrutineeExtension, branchStoreTyping, scrutineeEvaluation,
        scrutineeReducible⟩ :=
          scrutineeIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at scrutineeReducible
      cases scrutineeReducible with
      | constructed constructorLookup payloadTyping =>
          obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
            payloadTypeLookup⟩ :=
              DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                constructorLookup
          change _[_]? = some _ at definitionLookup
          rw [definitionLookup] at runtimeDefinitionLookup
          cases runtimeDefinitionLookup
          have payloadReducible :=
            (definitionsWellFormed.constructorPayload_of_lookup
              constructorLookup).reducible payloadTyping
          obtain ⟨branch, resultWorld, resultStore, result, branchLookup,
            branchExtension, resultStoreTyping, branchEvaluation,
            resultReducible⟩ :=
              branchesIH
                definitionsWellFormed
                (environmentReducible.weaken scrutineeExtension)
                branchStoreTyping payloadTypeLookup payloadReducible
          exact ⟨resultWorld, resultStore, result,
            scrutineeExtension.trans branchExtension, resultStoreTyping,
            .matchData scrutineeEvaluation rfl branchLookup branchEvaluation,
            resultReducible⟩
  | unary operandTyping operandIH =>
      obtain ⟨resultWorld, resultStore, operandValue, extension,
        resultStoreTyping, operandEvaluation, operandReducible⟩ :=
          operandIH definitionsWellFormed environmentReducible storeTyping
      obtain ⟨result, applied, _⟩ :=
        UnaryOp.apply_total_of_type _ operandValue operandReducible.hasType.type_eq
      exact ⟨resultWorld, resultStore, result, extension, resultStoreTyping,
        .unary operandEvaluation applied,
        unary_apply_result_reducible (definitions := _) applied⟩
  | binary leftTyping rightTyping leftIH rightIH =>
      obtain ⟨rightWorld, rightStore, leftValue, leftExtension,
        rightStoreTyping, leftEvaluation, leftReducible⟩ :=
          leftIH definitionsWellFormed environmentReducible storeTyping
      obtain ⟨resultWorld, resultStore, rightValue, rightExtension,
        resultStoreTyping, rightEvaluation, rightReducible⟩ :=
          rightIH definitionsWellFormed
            (environmentReducible.weaken leftExtension) rightStoreTyping
      obtain ⟨result, applied, _⟩ :=
        BinaryOp.apply_total_of_types _ leftValue rightValue
          leftReducible.hasType.type_eq rightReducible.hasType.type_eq
      exact ⟨resultWorld, resultStore, result,
        leftExtension.trans rightExtension, resultStoreTyping,
        .binary leftEvaluation rightEvaluation applied,
        binary_apply_result_reducible (definitions := _) applied⟩
  | letE boundTyping bodyTyping boundIH bodyIH =>
      obtain ⟨bodyWorld, bodyStore, boundValue, boundExtension,
        bodyStoreTyping, boundEvaluation, boundReducible⟩ :=
          boundIH definitionsWellFormed environmentReducible storeTyping
      obtain ⟨resultWorld, resultStore, result, bodyExtension,
        resultStoreTyping, bodyEvaluation, resultReducible⟩ :=
          bodyIH
            definitionsWellFormed
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
          conditionIH definitionsWellFormed environmentReducible storeTyping
      simp only [ReducibleValue] at conditionReducible
      obtain ⟨decision, rfl⟩ := conditionReducible
      cases decision with
      | false =>
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              elseIH definitionsWellFormed
                (environmentReducible.weaken conditionExtension)
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            conditionExtension.trans branchExtension, resultStoreTyping,
            .ifFalse conditionEvaluation branchEvaluation, resultReducible⟩
      | true =>
          obtain ⟨resultWorld, resultStore, result, branchExtension,
            resultStoreTyping, branchEvaluation, resultReducible⟩ :=
              thenIH definitionsWellFormed
                (environmentReducible.weaken conditionExtension)
                branchStoreTyping
          exact ⟨resultWorld, resultStore, result,
            conditionExtension.trans branchExtension, resultStoreTyping,
            .ifTrue conditionEvaluation branchEvaluation, resultReducible⟩
  | nil =>
      simp_all
  | cons branchTyping branchesTyping branchIH branchesIH =>
      rename_i definitionsWellFormed world environment store index
        payloadType payloadValue
        environmentReducible storeTyping payloadLookup payloadReducible
      cases index with
      | zero =>
          simp at payloadLookup
          cases payloadLookup
          obtain ⟨finalWorld, finalStore, result, extension,
            finalStoreTyping, evaluation, resultReducible⟩ :=
              branchIH definitionsWellFormed
                (.cons payloadReducible environmentReducible) storeTyping
          exact ⟨_, finalWorld, finalStore, result, rfl, extension,
            finalStoreTyping, evaluation, resultReducible⟩
      | succ index =>
          obtain ⟨branch, finalWorld, finalStore, result, branchLookup,
            extension, finalStoreTyping, evaluation, resultReducible⟩ :=
              branchesIH definitionsWellFormed environmentReducible storeTyping
                (by simpa using payloadLookup) payloadReducible
          exact ⟨branch, finalWorld, finalStore, result,
            by simpa using branchLookup, extension, finalStoreTyping,
            evaluation, resultReducible⟩

theorem RuntimeValueHasType.reducible
    {definitions : DataEnvironment}
    {world : StoreTyping} {value : Value} {type : Ty}
    (typing : RuntimeValueHasType world value type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ReducibleValue world type value definitions := by
  revert definitionsWellFormed
  apply RuntimeValueHasType.rec
      (world := world)
      (motive_1 := fun value type relationDefinitions _ =>
        relationDefinitions.WellFormed →
          ReducibleValue world type value relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        relationDefinitions.WellFormed →
          ReducibleEnvironment world environment context relationDefinitions)
      (t := typing)
  case unit => intros; simp only [ReducibleValue]
  case bool =>
    intros
    simp only [ReducibleValue]
    exact ⟨_, rfl⟩
  case word =>
    intros
    simp only [ReducibleValue]
    exact ⟨_, rfl⟩
  case pair =>
    intro _ _ _ _ _ _ _ leftIH rightIH wellFormed
    simp only [ReducibleValue]
    exact ⟨_, _, rfl, leftIH wellFormed, rightIH wellFormed⟩
  case inLeft =>
    intro _ _ _ _ _ payloadIH wellFormed
    simp only [ReducibleValue]
    exact .inl ⟨_, rfl, payloadIH wellFormed⟩
  case inRight =>
    intro _ _ _ _ _ payloadIH wellFormed
    simp only [ReducibleValue]
    exact .inr ⟨_, rfl, payloadIH wellFormed⟩
  case closure =>
    intro _ _ _ _ _ _ environmentTyping bodyTyping environmentIH wellFormed
    simp only [ReducibleValue]
    exact ⟨_, _, _, rfl, environmentTyping, bodyTyping,
      fun futureExtension futureStoreTyping argumentReducible =>
        reducibility_fundamental wellFormed bodyTyping
          (.cons argumentReducible
            ((environmentIH wellFormed).weaken futureExtension))
          futureStoreTyping⟩
  case cellRef =>
    intro _ _ _ found _
    simp only [ReducibleValue]
    exact ⟨_, rfl, found⟩
  case constructed =>
    intro _ _ _ _ lookup payloadTyping _ _
    exact .constructed lookup payloadTyping
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH wellFormed
    exact .cons (valueIH wellFormed) (environmentIH wellFormed)

theorem RuntimeEnvironmentHasTypes.reducible
    {definitions : DataEnvironment}
    {world : StoreTyping} {environment : Environment} {context : Context}
    (typing : RuntimeEnvironmentHasTypes world environment context definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ReducibleEnvironment world environment context definitions := by
  revert definitionsWellFormed
  apply RuntimeEnvironmentHasTypes.rec
      (world := world)
      (motive_1 := fun value type relationDefinitions _ =>
        relationDefinitions.WellFormed →
          ReducibleValue world type value relationDefinitions)
      (motive_2 := fun environment context relationDefinitions _ =>
        relationDefinitions.WellFormed →
          ReducibleEnvironment world environment context relationDefinitions)
      (t := typing)
  case unit => intros; simp only [ReducibleValue]
  case bool =>
    intros
    simp only [ReducibleValue]
    exact ⟨_, rfl⟩
  case word =>
    intros
    simp only [ReducibleValue]
    exact ⟨_, rfl⟩
  case pair =>
    intro _ _ _ _ _ _ _ leftIH rightIH wellFormed
    simp only [ReducibleValue]
    exact ⟨_, _, rfl, leftIH wellFormed, rightIH wellFormed⟩
  case inLeft =>
    intro _ _ _ _ _ payloadIH wellFormed
    simp only [ReducibleValue]
    exact .inl ⟨_, rfl, payloadIH wellFormed⟩
  case inRight =>
    intro _ _ _ _ _ payloadIH wellFormed
    simp only [ReducibleValue]
    exact .inr ⟨_, rfl, payloadIH wellFormed⟩
  case closure =>
    intro _ _ _ _ _ _ environmentTyping bodyTyping environmentIH wellFormed
    simp only [ReducibleValue]
    exact ⟨_, _, _, rfl, environmentTyping, bodyTyping,
      fun futureExtension futureStoreTyping argumentReducible =>
        reducibility_fundamental wellFormed bodyTyping
          (.cons argumentReducible
            ((environmentIH wellFormed).weaken futureExtension))
          futureStoreTyping⟩
  case cellRef =>
    intro _ _ _ found _
    simp only [ReducibleValue]
    exact ⟨_, rfl, found⟩
  case constructed =>
    intro _ _ _ _ lookup payloadTyping _ _
    exact .constructed lookup payloadTyping
  case nil => intros; exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ valueIH environmentIH wellFormed
    exact .cons (valueIH wellFormed) (environmentIH wellFormed)

theorem reducible_environment_evaluates
    {definitions : DataEnvironment}
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type definitions)
    (definitionsWellFormed : definitions.WellFormed)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentReducible :
      ReducibleEnvironment world environment context definitions)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, finalStore, value, extension,
    finalStoreTyping, evaluation, valueReducible⟩ :=
      reducibility_fundamental definitionsWellFormed typing
        environmentReducible storeTyping
  exact ⟨finalWorld, finalStore, value, extension, finalStoreTyping,
    evaluation, valueReducible.runtimeHasType⟩

theorem well_typed_evaluates
    {definitions : DataEnvironment}
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type definitions)
    (definitionsWellFormed : definitions.WellFormed)
    {world : StoreTyping} {environment : Environment} {store : Store}
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world store) :
    ∃ finalWorld finalStore value,
      WorldExtends world finalWorld ∧
      StoreHasTypes finalWorld finalStore ∧
      Evaluates environment store expr value finalStore ∧
      RuntimeValueHasType finalWorld value type definitions :=
  reducible_environment_evaluates typing definitionsWellFormed
    (environmentTyping.reducible definitionsWellFormed) storeTyping

theorem closed_well_typed_evaluates
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      Evaluates [] [] expr value finalStore ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, finalStore, value, _, finalStoreTyping,
    evaluation, valueTyping⟩ :=
      well_typed_evaluates typing definitionsWellFormed .nil .nil
  exact ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩

theorem closed_well_typed_runStateful_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type definitions := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing definitionsWellFormed
  obtain ⟨fuel, result⟩ := evaluation_runStateful_complete evaluation
  exact ⟨fuel, finalWorld, finalStore, value, result,
    finalStoreTyping, valueTyping⟩

theorem closed_well_typed_run_stateful_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ fuel finalWorld finalStore value,
      runStateful fuel (State.initial expr) = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type definitions :=
  closed_well_typed_runStateful_completes typing definitionsWellFormed

theorem closed_well_typed_runStateful_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type definitions ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore := by
  obtain ⟨finalWorld, finalStore, value,
    finalStoreTyping, evaluation, valueTyping⟩ :=
      closed_well_typed_evaluates typing definitionsWellFormed
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, finalWorld, finalStore, value,
    finalStoreTyping, valueTyping, completes⟩

theorem closed_well_typed_run_stateful_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value type definitions ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial expr) = .done value finalStore :=
  closed_well_typed_runStateful_has_sufficient_fuel typing definitionsWellFormed

theorem closed_well_typed_run_completes
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ fuel value,
      run fuel (State.initial expr) = .done value ∧
      ValueHasType value type definitions := by
  obtain ⟨fuel, finalWorld, finalStore, value, result, _, valueTyping⟩ :=
    closed_well_typed_runStateful_completes typing definitionsWellFormed
  exact ⟨fuel, value,
    by simp [run, result, StatefulRunResult.erase], valueTyping.erase⟩

theorem closed_well_typed_run_has_sufficient_fuel
    {definitions : DataEnvironment}
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type definitions)
    (definitionsWellFormed : definitions.WellFormed) :
    ∃ required value,
      ValueHasType value type definitions ∧
      ∀ fuel, required ≤ fuel →
        run fuel (State.initial expr) = .done value := by
  obtain ⟨required, finalWorld, finalStore, value, _, valueTyping,
    completes⟩ :=
      closed_well_typed_runStateful_has_sufficient_fuel
        typing definitionsWellFormed
  exact ⟨required, value, valueTyping.erase, fun fuel enough => by
    simp [run, completes fuel enough, StatefulRunResult.erase]⟩

/-! ## Typed CEK states -/

inductive FrameHasType
    (world : StoreTyping) :
    Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | unaryApply {definitions : DataEnvironment} {op : UnaryOp} :
      FrameHasType world (.unaryApply op) op.operandType op.resultType definitions
  | binaryRight
      {definitions : DataEnvironment}
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right op.rightType definitions →
      FrameHasType world (.binaryRight op right environment)
        op.leftType op.resultType definitions
  | binaryApply
      {definitions : DataEnvironment} {op : BinaryOp} {leftValue : Value} :
      RuntimeValueHasType world leftValue op.leftType definitions →
      FrameHasType world (.binaryApply op leftValue)
        op.rightType op.resultType definitions
  | ternarySecond
      {definitions : DataEnvironment} {op : TernaryOp}
      {second third : Expr} {environment : Environment} {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context second op.secondType definitions →
      HasType context third op.thirdType definitions →
      FrameHasType world (.ternarySecond op second third environment)
        op.firstType op.resultType definitions
  | ternaryThird
      {definitions : DataEnvironment} {op : TernaryOp}
      {firstValue : Value} {third : Expr} {environment : Environment}
      {context : Context} :
      RuntimeValueHasType world firstValue op.firstType definitions →
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context third op.thirdType definitions →
      FrameHasType world (.ternaryThird op firstValue third environment)
        op.secondType op.resultType definitions
  | ternaryApply
      {definitions : DataEnvironment} {op : TernaryOp}
      {firstValue secondValue : Value} :
      RuntimeValueHasType world firstValue op.firstType definitions →
      RuntimeValueHasType world secondValue op.secondType definitions →
      FrameHasType world (.ternaryApply op firstValue secondValue)
        op.thirdType op.resultType definitions
  | pairRight
      {definitions : DataEnvironment}
      {right : Expr} {environment : Environment} {context : Context}
      {leftType rightType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right rightType definitions →
      FrameHasType world (.pairRight right environment)
        leftType (.product leftType rightType) definitions
  | pairApply
      {definitions : DataEnvironment}
      {leftValue : Value} {leftType rightType : Ty} :
      RuntimeValueHasType world leftValue leftType definitions →
      FrameHasType world (.pairApply leftValue)
        rightType (.product leftType rightType) definitions
  | firstApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world .firstApply (.product leftType rightType) leftType
        definitions
  | secondApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world .secondApply (.product leftType rightType) rightType
        definitions
  | inLeftApply
      {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world (.inLeftApply rightType)
        leftType (.sum leftType rightType) definitions
  | inRightApply
      {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world (.inRightApply leftType)
        rightType (.sum leftType rightType) definitions
  | caseBranches
      {definitions : DataEnvironment}
      {leftBranch rightBranch : Expr} {environment : Environment}
      {context : Context} {leftType rightType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (leftType :: context) leftBranch resultType definitions →
      HasType (rightType :: context) rightBranch resultType definitions →
      FrameHasType world
        (.caseBranches leftBranch rightBranch environment)
        (.sum leftType rightType) resultType definitions
  | newCellApply {definitions : DataEnvironment} {elementType : Ty} :
      CellPayload elementType →
      FrameHasType world (.newCellApply elementType)
        elementType (.cell elementType) definitions
  | loadCellApply {definitions : DataEnvironment} {elementType : Ty} :
      CellPayload elementType →
      FrameHasType world .loadCellApply (.cell elementType) elementType definitions
  | storeCellValue
      {definitions : DataEnvironment}
      {valueExpr : Expr} {environment : Environment} {context : Context}
      {elementType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context valueExpr elementType definitions →
      CellPayload elementType →
      FrameHasType world (.storeCellValue valueExpr environment)
        (.cell elementType) .unit definitions
  | storeCellApply
      {definitions : DataEnvironment} {elementType : Ty} {location : Location} :
      world[location]? = some elementType →
      CellPayload elementType →
      FrameHasType world (.storeCellApply elementType location)
        elementType .unit definitions
  | constructApply
      {definitions : DataEnvironment}
      {constructor : ConstructorId} {payloadType : Ty} :
      definitions.lookupConstructorPayloadType? constructor = some payloadType →
      FrameHasType world (.constructApply constructor) payloadType
        (.namedData constructor.owner) definitions
  | matchDataApply
      {definitions : DataEnvironment}
      {dataType : DataTypeId} {definition : DataDefinition}
      {branches : List Expr} {environment : Environment} {context : Context}
      {resultType : Ty} :
      definitions.lookupDataType? dataType = some definition →
      RuntimeEnvironmentHasTypes world environment context definitions →
      BranchesHaveType context resultType definition.constructorPayloadTypes
        branches definitions →
      FrameHasType world (.matchDataApply dataType branches environment)
        (.namedData dataType) resultType definitions
  | applyArgument
      {definitions : DataEnvironment}
      {argument : Expr} {environment : Environment} {context : Context}
      {parameterType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context argument parameterType definitions →
      FrameHasType world (.applyArgument argument environment)
        (.function parameterType resultType) resultType definitions
  | applyClosure
      {definitions : DataEnvironment}
      {parameterType resultType : Ty} {body : Expr}
      {environment : Environment} {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (parameterType :: context) body resultType definitions →
      FrameHasType world
        (.applyClosure parameterType resultType body environment)
        parameterType resultType definitions
  | letBody
      {definitions : DataEnvironment}
      {body : Expr} {environment : Environment} {context : Context}
      {inputType outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (inputType :: context) body outputType definitions →
      FrameHasType world (.letBody body environment) inputType outputType
        definitions
  | ifBranches
      {definitions : DataEnvironment}
      {thenBranch elseBranch : Expr} {environment : Environment}
      {context : Context} {outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context thenBranch outputType definitions →
      HasType context elseBranch outputType definitions →
      FrameHasType world
        (.ifBranches thenBranch elseBranch environment) .bool outputType definitions

inductive ContinuationHasType
    (world : StoreTyping) :
    List Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | nil {definitions : DataEnvironment} {type : Ty} :
      ContinuationHasType world [] type type definitions
  | cons
      {definitions : DataEnvironment}
      {frame : Frame} {continuation : List Frame}
      {inputType middleType outputType : Ty} :
      FrameHasType world frame inputType middleType definitions →
      ContinuationHasType world continuation middleType outputType definitions →
      ContinuationHasType world (frame :: continuation) inputType outputType
        definitions

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
  | newCellApply payload => exact .newCellApply payload
  | loadCellApply payload => exact .loadCellApply payload
  | storeCellValue environmentTyping valueTyping payload =>
      exact .storeCellValue (environmentTyping.weaken extension)
        valueTyping payload
  | storeCellApply found payload =>
      exact .storeCellApply (extension.lookup found) payload
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

inductive StateHasType :
    State → Ty → (definitions : DataEnvironment := []) → Prop where
  | eval
      {definitions : DataEnvironment}
      {world : StoreTyping} {expr : Expr} {environment : Environment}
      {context : Context} {continuation : List Frame} {store : Store}
      {controlType resultType : Ty} :
      StoreHasTypes world store →
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context expr controlType definitions →
      ContinuationHasType world continuation controlType resultType definitions →
      StateHasType
        ⟨.eval expr environment, continuation, store⟩ resultType definitions
  | ret
      {definitions : DataEnvironment}
      {world : StoreTyping} {value : Value} {continuation : List Frame}
      {store : Store} {controlType resultType : Ty} :
      StoreHasTypes world store →
      RuntimeValueHasType world value controlType definitions →
      ContinuationHasType world continuation controlType resultType definitions →
      StateHasType ⟨.ret value, continuation, store⟩ resultType definitions

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
          | newCell initializerTyping payload =>
              exact .eval storeTyping environmentTyping initializerTyping
                (.cons (.newCellApply payload) continuationTyping)
  | @applyNewCell elementType initialValue continuation store =>
      cases stateTyping with
      | @ret _ world _ _ _ _ _ storeTyping valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | @newCellApply _ elementType payload =>
                  let futureWorld := world ++ [elementType]
                  have extension : WorldExtends world futureWorld :=
                    ⟨[elementType], rfl⟩
                  have futureStoreTyping :
                      StoreHasTypes futureWorld (store.allocate initialValue).1 := by
                    simpa [futureWorld] using
                      storeTyping.allocate payload
                        (payload.valueHasType_rebase valueTyping.erase)
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
                        (storedPayload.runtimeValueHasType
                          (definitions := definitions) storedTyping)
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
              | storeCellApply found payload =>
                  exact .ret
                    (storeTyping.write found
                      (payload.valueHasType_rebase valueTyping.erase) written)
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
      | eval _ _ exprTyping _ => cases exprTyping
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
  .eval .nil .nil typing .nil

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
      StoreHasTypes finalWorld finalStore ∧
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
      StoreHasTypes finalWorld finalStore ∧
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
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  exact well_typed_runStateful_preserves_result_type
    (initial_state_has_type wellTyped.bodyHasType) result

theorem Program.checked_run_stateful_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value} {finalStore : Store}
    (checked : program.check = true)
    (result : program.runStateful fuel = .done value finalStore) :
    ∃ finalWorld,
      StoreHasTypes finalWorld finalStore ∧
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
    (checked : program.check = true) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_completes wellTyped.bodyHasType
      wellTyped.dataDefinitionsWellFormed

theorem Program.checked_run_stateful_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel finalWorld finalStore value,
      program.runStateful fuel = .done value finalStore ∧
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions :=
  Program.checked_runStateful_completes checked

theorem Program.checked_run_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel value,
      program.run fuel = .done value ∧
      ValueHasType value program.resultType program.dataDefinitions := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.run] using
    closed_well_typed_run_completes wellTyped.bodyHasType
      wellTyped.dataDefinitionsWellFormed

theorem Program.checked_runStateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.runStateful] using
    closed_well_typed_runStateful_has_sufficient_fuel
      wellTyped.bodyHasType wellTyped.dataDefinitionsWellFormed

theorem Program.checked_run_stateful_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required finalWorld finalStore value,
      StoreHasTypes finalWorld finalStore ∧
      RuntimeValueHasType finalWorld value program.resultType
        program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.runStateful fuel = .done value finalStore :=
  Program.checked_runStateful_has_sufficient_fuel checked

theorem Program.checked_run_has_sufficient_fuel
    {program : Program}
    (checked : program.check = true) :
    ∃ required value,
      ValueHasType value program.resultType program.dataDefinitions ∧
      ∀ fuel, required ≤ fuel →
        program.run fuel = .done value := by
  let wellTyped := Program.check_full_sound checked
  simpa [Program.run] using
    closed_well_typed_run_has_sufficient_fuel wellTyped.bodyHasType
      wellTyped.dataDefinitionsWellFormed

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
