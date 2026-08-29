import Solcore.Core.Host
import Solcore.Core.Safety

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

@[simp] theorem hostEnvironment_hasTypes
    (world : StoreTyping)
    (definitions : DataEnvironment := []) :
    HostRuntimeEnvironmentHasTypes world hostEnvironment hostContext definitions :=
  .cons .hostFunction (.cons .hostFunction (.cons .hostFunction .nil))

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

/-- Cell payload types cannot contain host capabilities, so their structural
typing can be recovered before writing them to the Core-local store. -/
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

end Solcore.Core
