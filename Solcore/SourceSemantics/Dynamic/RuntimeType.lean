import Solcore.SourceSemantics.Dynamic.Value

/-! Source runtime type compatibility erases staging recursively. Canonical
shallow metadata remains raw; a runtime key guard compares its normalized
view with the normalized expected type. Defaults and diagnostics retain the
original expected metadata. No runtime value codec or evaluator is imported. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Dynamic
open Frontend Frontend.SourceInference TypeSystem

/-- Erase availability annotations throughout a source type. -/
@[simp] def runtimeType : Ty → Ty
  | .variable id => .variable id
  | .parameter id => .parameter id
  | .constructor id => .constructor id
  | .application function argument => .application (runtimeType function) (runtimeType argument)
  | .function parameter result => .function (runtimeType parameter) (runtimeType result)
  | .product left right => .product (runtimeType left) (runtimeType right)
  | .mapping key value => .mapping (runtimeType key) (runtimeType value)
  | .proxy inner => .proxy (runtimeType inner)
  | .comptime inner => runtimeType inner
  | .error => .error

@[simp] theorem runtimeType_idempotent (type : Ty) : runtimeType (runtimeType type) = runtimeType type := by
  induction type <;> simp_all [runtimeType]

/-- Canonical shallow runtime type of every mathematical source value. -/
inductive ValueRuntimeType : Value → Ty → Prop where
  | unit : ValueRuntimeType .unit .unit
  | bool (value : Bool) : ValueRuntimeType (.bool value) .bool
  | word (value : Core.Word) : ValueRuntimeType (.word value) .word
  | integer (value : Int) : ValueRuntimeType (.integer value) .integer
  | product
      {left right : Value} {leftType rightType : Ty}
      (left_type : ValueRuntimeType left leftType)
      (right_type : ValueRuntimeType right rightType) :
      ValueRuntimeType (.product left right) (.product leftType rightType)
  | proxy (inner : Ty) : ValueRuntimeType (.proxy inner) (.proxy inner)
  | constructed
      (instantiation : DataConstructorInstantiation) (arguments : List Value) :
      ValueRuntimeType (.constructed instantiation arguments)
        instantiation.resultType
  | mapping (keyType valueType : Ty) (entries : List (Value × Value)) :
      ValueRuntimeType (.mapping keyType valueType entries)
        (.mapping keyType valueType)
  | closure (function : Closure) :
      ValueRuntimeType (.closure function)
        (.function
          (Ty.productMany (function.parameters.map fun binder => binder.scheme.body))
          function.resultType)
  | global (function : GlobalFunction) :
      ValueRuntimeType (.global function) function.instantiation.type
  | builtin (function : BuiltinFunction) :
      ValueRuntimeType (.builtin function) function.id.type

/-- The retained shallow metadata of a mathematical value is unique. -/
theorem ValueRuntimeType.functional {value : Value} {first second : Ty}
    (typed : ValueRuntimeType value first) (other : ValueRuntimeType value second) : first = second := by
  induction typed generalizing second with
  | unit | bool | word | integer | proxy | constructed | mapping | closure | global | builtin => cases other; rfl
  | product left right first second =>
    cases other with
    | product a b => simp only [first a, second b]

/-- A key passes its runtime type guard when its canonical shallow type
and the retained expected type have the same runtime shape. -/
inductive ValueRuntimeTypeMatches (value : Value) (expected : Ty) : Prop where
  | intro {actual : Ty} (typed : ValueRuntimeType value actual)
      (same : runtimeType actual = runtimeType expected) : ValueRuntimeTypeMatches value expected

/-- Existing exact type receipts imply the runtime guard. -/
theorem ValueRuntimeType.matches {value : Value} {type : Ty} (typed : ValueRuntimeType value type) :
    ValueRuntimeTypeMatches value type := .intro typed rfl

namespace ValueRuntimeTypeMatches

theorem of_view {value : Value} {actual expected : Ty}
    (typed : ValueRuntimeType value actual) (same : runtimeType actual = runtimeType expected) :
    ValueRuntimeTypeMatches value expected := .intro typed same

theorem agrees {value : Value} {actual expected : Ty}
    (accepted : ValueRuntimeTypeMatches value expected) (typed : ValueRuntimeType value actual) :
    runtimeType actual = runtimeType expected := by
  cases accepted with
  | intro canonical same => exact (congrArg runtimeType (typed.functional canonical)).trans same

theorem bool (value : Bool) : ValueRuntimeTypeMatches (.bool value) .bool := (ValueRuntimeType.bool value).matches
theorem word (value : Core.Word) : ValueRuntimeTypeMatches (.word value) .word := (ValueRuntimeType.word value).matches
theorem integer (value : Int) : ValueRuntimeTypeMatches (.integer value) .integer := (ValueRuntimeType.integer value).matches

end ValueRuntimeTypeMatches
end Solcore.SourceSemantics.Dynamic
