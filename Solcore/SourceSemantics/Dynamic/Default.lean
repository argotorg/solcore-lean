import Solcore.SourceSemantics.Dynamic.Typing

/-!
Declarative default values for the source runtime domain.

The rules cover exactly the source type forms for which execution can create a
default without choosing a nominal constructor or synthesizing code: the four
primitive types, products, proxies, mappings, and staging wrappers.  The
relation is independent of the executable default-value function.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open TypeSystem

/-- Source types which have a canonical runtime default. -/
inductive Defaultable : Ty → Prop where
  | unit : Defaultable .unit
  | bool : Defaultable .bool
  | word : Defaultable .word
  | integer : Defaultable .integer
  | product {left right : Ty}
      (left_defaultable : Defaultable left)
      (right_defaultable : Defaultable right) :
      Defaultable (.product left right)
  | proxy (inner : Ty) : Defaultable (.proxy inner)
  | mapping (keyType valueType : Ty) :
      Defaultable (.mapping keyType valueType)
  | comptime {inner : Ty} (inner_defaultable : Defaultable inner) :
      Defaultable (.comptime inner)

/-- Exact canonical default denoted by one defaultable source type. -/
inductive DefaultValue : Ty → Value → Prop where
  | unit : DefaultValue .unit .unit
  | bool : DefaultValue .bool (.bool false)
  | word : DefaultValue .word (.word Core.Word.zero)
  | integer : DefaultValue .integer (.integer 0)
  | product
      {leftType rightType : Ty} {left right : Value}
      (left_default : DefaultValue leftType left)
      (right_default : DefaultValue rightType right) :
      DefaultValue (.product leftType rightType) (.product left right)
  | proxy (inner : Ty) : DefaultValue (.proxy inner) (.proxy inner)
  | mapping (keyType valueType : Ty) :
      DefaultValue (.mapping keyType valueType)
        (.mapping keyType valueType [])
  | comptime
      {inner : Ty} {value : Value}
      (inner_default : DefaultValue inner value) :
      DefaultValue (.comptime inner) value

namespace DefaultValue

/-- Every canonical default has its indexing source type. -/
theorem hasType
    {context : Context} {heap : Heap} {type : Ty} {value : Value}
    (defaultValue : DefaultValue type value) :
    ValueHasType context heap value type := by
  induction defaultValue with
  | unit => exact .unit
  | bool => exact .bool false
  | word => exact .word Core.Word.zero
  | integer => exact .integer 0
  | product _ _ left_ih right_ih => exact .product left_ih right_ih
  | proxy inner => exact .proxy inner
  | mapping keyType valueType =>
      exact .mapping (.nil keyType valueType)
  | comptime _ inner_ih => exact .comptime inner_ih

/-- Default existence implies the structural defaultability classification. -/
theorem defaultable
    {type : Ty} {value : Value} (defaultValue : DefaultValue type value) :
    Defaultable type := by
  induction defaultValue with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left_ih right_ih => exact .product left_ih right_ih
  | proxy inner => exact .proxy inner
  | mapping keyType valueType => exact .mapping keyType valueType
  | comptime _ inner_ih => exact .comptime inner_ih

/-- The canonical default is unique. -/
theorem functional
    {type : Ty} {left right : Value}
    (leftDefault : DefaultValue type left)
    (rightDefault : DefaultValue type right) :
    left = right := by
  induction leftDefault generalizing right with
  | unit => cases rightDefault; rfl
  | bool => cases rightDefault; rfl
  | word => cases rightDefault; rfl
  | integer => cases rightDefault; rfl
  | product leftDefault rightDefault left_ih right_ih =>
      cases rightDefault with
      | product otherLeft otherRight =>
          rw [left_ih otherLeft, right_ih otherRight]
  | proxy inner => cases rightDefault; rfl
  | mapping keyType valueType => cases rightDefault; rfl
  | comptime innerDefault ih =>
      cases rightDefault with
      | comptime otherDefault => exact ih otherDefault

/-- Flexible variables do not acquire an arbitrary default. -/
theorem not_variable (metavariable : TypeVarId) (value : Value) :
    ¬ DefaultValue (.variable metavariable) value := by
  intro defaultValue
  cases defaultValue

/-- Rigid parameters do not acquire an arbitrary default. -/
theorem not_parameter (parameter : TypeParameterId) (value : Value) :
    ¬ DefaultValue (.parameter parameter) value := by
  intro defaultValue
  cases defaultValue

/-- Function values require code provenance and are never synthesized as
defaults. -/
theorem not_function (parameter result : Ty) (value : Value) :
    ¬ DefaultValue (.function parameter result) value := by
  intro defaultValue
  cases defaultValue

/-- Recovery types have no dynamic default. -/
theorem not_error (value : Value) : ¬ DefaultValue .error value := by
  intro defaultValue
  cases defaultValue

end DefaultValue

namespace Defaultable

/-- Every classified type has a canonical value. -/
theorem exists_default {type : Ty} (defaultable : Defaultable type) :
    ∃ value, DefaultValue type value := by
  induction defaultable with
  | unit => exact ⟨.unit, .unit⟩
  | bool => exact ⟨.bool false, .bool⟩
  | word => exact ⟨.word Core.Word.zero, .word⟩
  | integer => exact ⟨.integer 0, .integer⟩
  | product _ _ left_ih right_ih =>
      rcases left_ih with ⟨left, leftDefault⟩
      rcases right_ih with ⟨right, rightDefault⟩
      exact ⟨.product left right, .product leftDefault rightDefault⟩
  | proxy inner => exact ⟨.proxy inner, .proxy inner⟩
  | mapping keyType valueType =>
      exact ⟨.mapping keyType valueType [], .mapping keyType valueType⟩
  | comptime _ inner_ih =>
      rcases inner_ih with ⟨value, defaultValue⟩
      exact ⟨value, .comptime defaultValue⟩

end Defaultable

theorem defaultValue_exists_iff (type : Ty) :
    (∃ value, DefaultValue type value) ↔ Defaultable type := by
  constructor
  · rintro ⟨value, defaultValue⟩
    exact defaultValue.defaultable
  · intro defaultable
    exact defaultable.exists_default

end Solcore.SourceSemantics.Dynamic
