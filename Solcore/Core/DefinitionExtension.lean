import Solcore.Core.Safety

/-! Appending generated administrative definitions preserves every existing
data identity and static/runtime typing derivation. Fresh definitions still
require their own registration and typing evidence in the extended environment. -/
set_option autoImplicit false
namespace Solcore.Core

def DataEnvironment.Extends (initial future : DataEnvironment) : Prop :=
  ∃ suffix, future = initial ++ suffix

namespace DataEnvironment.Extends
theorem refl (definitions : DataEnvironment) : Extends definitions definitions := ⟨[], by simp⟩
theorem append (definitions suffix : DataEnvironment) : Extends definitions (definitions ++ suffix) := ⟨suffix, rfl⟩
theorem trans {first second third : DataEnvironment} (left : Extends first second) (right : Extends second third) :
    Extends first third := by
  obtain ⟨a, rfl⟩ := left
  obtain ⟨b, rfl⟩ := right
  exact ⟨a ++ b, by simp only [List.append_assoc]⟩
theorem lookup {initial future : DataEnvironment} (extension : Extends initial future)
    {index : Nat} {definition : DataDefinition} (found : initial[index]? = some definition) :
    future[index]? = some definition := by
  obtain ⟨suffix, rfl⟩ := extension
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found
theorem data_lookup {initial future : DataEnvironment} (extension : Extends initial future)
    {identity : DataTypeId} {definition : DataDefinition} (found : initial.lookupDataType? identity = some definition) :
    future.lookupDataType? identity = some definition := extension.lookup found
theorem constructor_lookup {initial future : DataEnvironment} (extension : Extends initial future)
    {constructor : ConstructorId} {payload : Ty} (found : initial.lookupConstructorPayloadType? constructor = some payload) :
    future.lookupConstructorPayloadType? constructor = some payload := by
  obtain ⟨definition, selected, payloadFound⟩ := DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp found
  exact DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mpr ⟨definition, extension.data_lookup selected, payloadFound⟩
end DataEnvironment.Extends

theorem Ty.WellFormed.extend_definitions {initial future : DataEnvironment} {type : Ty}
    (typed : type.WellFormed initial) (extension : initial.Extends future) : type.WellFormed future := by
  induction typed with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .product left right
  | function _ _ parameter result => exact .function parameter result
  | sum _ _ left right => exact .sum left right
  | cell _ element => exact .cell element
  | namedData found => exact .namedData (extension.lookup found)

theorem HasType.extend_definitions {initial future : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type initial) (extension : initial.Extends future) :
    HasType context expression type future := by
  induction typed using HasType.rec
      (motive_2 := fun context type payloads branches definitions _ =>
        ∀ {future}, definitions.Extends future → BranchesHaveType context type payloads branches future)
      generalizing future with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | var found => exact .var found
  | pair _ _ left right => exact .pair (left extension) (right extension)
  | first _ child => exact .first (child extension)
  | second _ child => exact .second (child extension)
  | lambda parameter result _ child =>
    exact .lambda (parameter.extend_definitions extension) (result.extend_definitions extension) (child extension)
  | apply _ _ function argument => exact .apply (function extension) (argument extension)
  | inLeft right _ child => exact .inLeft (right.extend_definitions extension) (child extension)
  | inRight left _ child => exact .inRight (left.extend_definitions extension) (child extension)
  | caseE _ _ _ scrutinee left right => exact .caseE (scrutinee extension) (left extension) (right extension)
  | newCell _ child => exact .newCell (child extension)
  | loadCell _ child => exact .loadCell (child extension)
  | storeCell _ _ reference value => exact .storeCell (reference extension) (value extension)
  | construct found _ child => exact .construct (extension.constructor_lookup found) (child extension)
  | matchData found result _ _ scrutinee branches =>
    exact .matchData (extension.data_lookup found) (result.extend_definitions extension) (scrutinee extension) (branches extension)
  | unary _ child => exact .unary (child extension)
  | binary _ _ left right => exact .binary (left extension) (right extension)
  | ternary _ _ _ first second third => exact .ternary (first extension) (second extension) (third extension)
  | letE _ _ value body => exact .letE (value extension) (body extension)
  | ifE _ _ _ condition yes no => exact .ifE (condition extension) (yes extension) (no extension)
  | nil => exact .nil
  | cons _ _ head tail => exact .cons (head (by assumption)) (tail (by assumption))

theorem RuntimeValueHasType.extend_definitions {initial future : DataEnvironment} {world : StoreTyping}
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type initial)
    (extension : initial.Extends future) : RuntimeValueHasType world value type future := by
  induction typed using RuntimeValueHasType.rec
      (motive_2 := fun environment context definitions _ =>
        ∀ {future}, definitions.Extends future → RuntimeEnvironmentHasTypes world environment context future)
      generalizing future with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | pair _ _ left right => exact .pair (left extension) (right extension)
  | inLeft _ child => exact .inLeft (child extension)
  | inRight _ child => exact .inRight (child extension)
  | closure _ body environment => exact .closure (environment extension) (body.extend_definitions extension)
  | cellRef found => exact .cellRef found
  | constructed found _ child => exact .constructed (extension.constructor_lookup found) (child extension)
  | nil => exact .nil
  | cons _ _ head tail => exact .cons (head (by assumption)) (tail (by assumption))

theorem RuntimeEnvironmentHasTypes.extend_definitions {initial future : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Context} (typed : RuntimeEnvironmentHasTypes world environment context initial)
    (extension : initial.Extends future) : RuntimeEnvironmentHasTypes world environment context future := by
  induction typed using RuntimeEnvironmentHasTypes.rec (motive_1 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => exact .nil
  | cons head _ _ tail => exact .cons (head.extend_definitions extension) (tail extension)

theorem RuntimeStoreHasTypes.extend_definitions {initial future : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store initial) (extension : initial.Extends future) :
    RuntimeStoreHasTypes world store future := by
  refine ⟨typed.length_eq, ?_⟩
  intro location type found
  obtain ⟨value, read, valueTyped⟩ := typed.lookup found
  exact ⟨value, read, valueTyped.extend_definitions extension⟩

end Solcore.Core
