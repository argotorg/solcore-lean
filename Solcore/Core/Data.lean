import Solcore.Core.Syntax

set_option autoImplicit false

namespace Solcore.Core

namespace DataEnvironment

def lookupDataType?
    (definitions : DataEnvironment)
    (dataType : DataTypeId) :
    Option DataDefinition :=
  definitions[dataType.index]?

def lookupConstructorPayloadType?
    (definitions : DataEnvironment)
    (constructor : ConstructorId) :
    Option Ty := do
  let definition ← definitions.lookupDataType? constructor.owner
  definition.constructorPayloadTypes[constructor.index]?

theorem lookupDataType?_eq_some_iff
    {definitions : DataEnvironment}
    {dataType : DataTypeId}
    {definition : DataDefinition} :
    definitions.lookupDataType? dataType = some definition ↔
      definitions[dataType.index]? = some definition :=
  Iff.rfl

theorem lookupConstructorPayloadType?_eq_some_iff
    {definitions : DataEnvironment}
    {constructor : ConstructorId}
    {payloadType : Ty} :
    definitions.lookupConstructorPayloadType? constructor = some payloadType ↔
      ∃ definition,
        definitions[constructor.owner.index]? = some definition ∧
        definition.constructorPayloadTypes[constructor.index]? = some payloadType := by
  simp only [lookupConstructorPayloadType?, lookupDataType?]
  cases lookup : definitions[constructor.owner.index]? with
  | none => simp
  | some definition => simp

theorem lookupConstructorPayloadType?_owner
    {definitions : DataEnvironment}
    {constructor : ConstructorId}
    {payloadType : Ty}
    (lookup :
      definitions.lookupConstructorPayloadType? constructor = some payloadType) :
    ∃ definition, definitions[constructor.owner.index]? = some definition := by
  obtain ⟨definition, ownerLookup, _⟩ :=
    lookupConstructorPayloadType?_eq_some_iff.mp lookup
  exact ⟨definition, ownerLookup⟩

theorem lookupConstructorPayloadType?_unique
    {definitions : DataEnvironment}
    {constructor : ConstructorId}
    {left right : Ty}
    (leftLookup :
      definitions.lookupConstructorPayloadType? constructor = some left)
    (rightLookup :
      definitions.lookupConstructorPayloadType? constructor = some right) :
    left = right := by
  rw [leftLookup] at rightLookup
  exact Option.some.inj rightLookup

theorem lookupConstructorPayloadType?_eq_none_of_empty_definition
    {definitions : DataEnvironment}
    {dataType : DataTypeId}
    {definition : DataDefinition}
    {constructor : ConstructorId}
    (owner : constructor.owner = dataType)
    (definitionLookup :
      definitions.lookupDataType? dataType = some definition)
    (empty : definition.constructorPayloadTypes = []) :
    definitions.lookupConstructorPayloadType? constructor = none := by
  subst dataType
  simp [lookupConstructorPayloadType?, definitionLookup, empty]

end DataEnvironment

namespace Ty

inductive WellFormed (definitions : DataEnvironment) : Ty → Prop where
  | unit : WellFormed definitions .unit
  | bool : WellFormed definitions .bool
  | word : WellFormed definitions .word
  | product {left right : Ty} :
      WellFormed definitions left →
      WellFormed definitions right →
      WellFormed definitions (.product left right)
  | function {parameter result : Ty} :
      WellFormed definitions parameter →
      WellFormed definitions result →
      WellFormed definitions (.function parameter result)
  | sum {left right : Ty} :
      WellFormed definitions left →
      WellFormed definitions right →
      WellFormed definitions (.sum left right)
  | cell {elementType : Ty} :
      WellFormed definitions elementType →
      WellFormed definitions (.cell elementType)
  | namedData {dataType : DataTypeId} {definition : DataDefinition} :
      definitions[dataType.index]? = some definition →
      WellFormed definitions (.namedData dataType)

def isWellFormed (definitions : DataEnvironment) : Ty → Bool
  | .unit
  | .bool
  | .word => true
  | .product left right
  | .function left right
  | .sum left right =>
      left.isWellFormed definitions && right.isWellFormed definitions
  | .cell elementType => elementType.isWellFormed definitions
  | .namedData dataType => (definitions[dataType.index]?).isSome

theorem isWellFormed_sound
    {definitions : DataEnvironment}
    {type : Ty}
    (accepted : type.isWellFormed definitions = true) :
    WellFormed definitions type := by
  induction type with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product left right leftIH rightIH =>
      simp [isWellFormed] at accepted
      exact .product (leftIH accepted.1) (rightIH accepted.2)
  | function parameter result parameterIH resultIH =>
      simp [isWellFormed] at accepted
      exact .function (parameterIH accepted.1) (resultIH accepted.2)
  | sum left right leftIH rightIH =>
      simp [isWellFormed] at accepted
      exact .sum (leftIH accepted.1) (rightIH accepted.2)
  | cell elementType elementIH =>
      exact .cell (elementIH accepted)
  | namedData dataType =>
      obtain ⟨definition, lookup⟩ := Option.isSome_iff_exists.mp accepted
      exact .namedData lookup

theorem isWellFormed_complete
    {definitions : DataEnvironment}
    {type : Ty}
    (wellFormed : WellFormed definitions type) :
    type.isWellFormed definitions = true := by
  induction wellFormed with
  | unit
  | bool
  | word => rfl
  | product leftWellFormed rightWellFormed leftIH rightIH
  | function leftWellFormed rightWellFormed leftIH rightIH
  | sum leftWellFormed rightWellFormed leftIH rightIH =>
      simp [isWellFormed, leftIH, rightIH]
  | cell elementWellFormed elementIH =>
      exact elementIH
  | namedData lookup =>
      exact Option.isSome_iff_exists.mpr ⟨_, lookup⟩

theorem isWellFormed_iff
    {definitions : DataEnvironment}
    {type : Ty} :
    type.isWellFormed definitions = true ↔ WellFormed definitions type :=
  ⟨isWellFormed_sound, isWellFormed_complete⟩

end Ty

/-- Constructor payloads use the same well-formed types as ordinary values,
including functions and references. Runtime typing checks stored values in
one shared world; data declarations impose no separate payload restriction. -/
abbrev ConstructorPayload (definitions : DataEnvironment) (type : Ty) : Prop :=
  Ty.WellFormed definitions type

namespace ConstructorPayload

export Ty.WellFormed (unit bool word product function sum cell namedData)

end ConstructorPayload

namespace Ty

def isConstructorPayload (definitions : DataEnvironment) (type : Ty) : Bool :=
  type.isWellFormed definitions

theorem isConstructorPayload_sound
    {definitions : DataEnvironment}
    {type : Ty}
    (accepted : type.isConstructorPayload definitions = true) :
    ConstructorPayload definitions type :=
  isWellFormed_sound accepted

theorem isConstructorPayload_complete
    {definitions : DataEnvironment}
    {type : Ty}
    (payload : ConstructorPayload definitions type) :
    type.isConstructorPayload definitions = true :=
  isWellFormed_complete payload

theorem isConstructorPayload_iff
    {definitions : DataEnvironment}
    {type : Ty} :
    type.isConstructorPayload definitions = true ↔
      ConstructorPayload definitions type :=
  isWellFormed_iff

end Ty

namespace CellPayload

theorem wellFormed
    {definitions : DataEnvironment}
    {type : Ty}
    (payload : CellPayload type) :
    Ty.WellFormed definitions type := by
  induction payload with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product leftPayload rightPayload leftIH rightIH =>
      exact .product leftIH rightIH
  | sum leftPayload rightPayload leftIH rightIH =>
      exact .sum leftIH rightIH

end CellPayload

namespace ConstructorPayload

theorem wellFormed
    {definitions : DataEnvironment}
    {type : Ty}
    (payload : ConstructorPayload definitions type) :
    Ty.WellFormed definitions type :=
  payload

end ConstructorPayload

namespace DataEnvironment

def WellFormed (definitions : DataEnvironment) : Prop :=
  ∀ definition ∈ definitions,
    ∀ payloadType ∈ definition.constructorPayloadTypes,
      ConstructorPayload definitions payloadType

def isWellFormed (definitions : DataEnvironment) : Bool :=
  definitions.all fun definition =>
    definition.constructorPayloadTypes.all fun payloadType =>
      payloadType.isConstructorPayload definitions

theorem isWellFormed_sound
    {definitions : DataEnvironment}
    (accepted : definitions.isWellFormed = true) :
    definitions.WellFormed := by
  intro definition definitionMember payloadType payloadMember
  have definitionAccepted :=
    (List.all_eq_true.mp accepted) definition definitionMember
  have payloadAccepted :=
    (List.all_eq_true.mp definitionAccepted) payloadType payloadMember
  exact Ty.isConstructorPayload_sound payloadAccepted

theorem isWellFormed_complete
    {definitions : DataEnvironment}
    (wellFormed : definitions.WellFormed) :
    definitions.isWellFormed = true := by
  apply List.all_eq_true.mpr
  intro definition definitionMember
  apply List.all_eq_true.mpr
  intro payloadType payloadMember
  exact Ty.isConstructorPayload_complete
    (wellFormed definition definitionMember payloadType payloadMember)

theorem isWellFormed_iff
    {definitions : DataEnvironment} :
    definitions.isWellFormed = true ↔ definitions.WellFormed :=
  ⟨isWellFormed_sound, isWellFormed_complete⟩

theorem WellFormed.constructorPayload_of_lookup
    {definitions : DataEnvironment}
    (wellFormed : definitions.WellFormed)
    {constructor : ConstructorId}
    {payloadType : Ty}
    (lookup :
      definitions.lookupConstructorPayloadType? constructor = some payloadType) :
    ConstructorPayload definitions payloadType := by
  obtain ⟨definition, definitionLookup, payloadLookup⟩ :=
    lookupConstructorPayloadType?_eq_some_iff.mp lookup
  obtain ⟨definitionBound, definitionGet⟩ :=
    List.getElem?_eq_some_iff.mp definitionLookup
  obtain ⟨payloadBound, payloadGet⟩ :=
    List.getElem?_eq_some_iff.mp payloadLookup
  apply wellFormed definition
  · exact List.mem_iff_getElem.mpr
      ⟨constructor.owner.index, definitionBound, definitionGet⟩
  · exact List.mem_iff_getElem.mpr
      ⟨constructor.index, payloadBound, payloadGet⟩

theorem WellFormed.constructorPayloadType_wellFormed
    {definitions : DataEnvironment}
    (wellFormed : definitions.WellFormed)
    {constructor : ConstructorId}
    {payloadType : Ty}
    (lookup :
      definitions.lookupConstructorPayloadType? constructor = some payloadType) :
    Ty.WellFormed definitions payloadType :=
  (wellFormed.constructorPayload_of_lookup lookup).wellFormed

end DataEnvironment

end Solcore.Core
