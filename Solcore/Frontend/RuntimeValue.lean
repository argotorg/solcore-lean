import Solcore.Core.Syntax
import Solcore.Syntax.Term
import Solcore.Resolved.Identity

/-!
Mixed values retain original source code and complete captures as inert data.
These definitions neither assign source-closure types nor evaluate or elaborate code.
Projection traverses finite value structure, not locations in a store.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- All Core forms mirror their recursive payloads; source code may have any original
syntax shape and carries exact ordered names/captures without validity assumptions. -/
inductive RuntimeValue where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | hostFunction (function : Core.HostFunction)
  | pair (left right : RuntimeValue)
  | coreClosure (parameterType resultType : Core.Ty) (body : Core.Expr) (captured : List RuntimeValue)
  | inLeft (rightType : Core.Ty) (payload : RuntimeValue)
  | inRight (leftType : Core.Ty) (payload : RuntimeValue)
  | cellRef (elementType : Core.Ty) (location : Core.Location)
  | constructed (constructor : Core.ConstructorId) (payload : RuntimeValue)
  | sourceClosure (source : Syntax.Expr) (owner : Resolved.DeclarationId)
      (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
  deriving Repr

/-- Preserve every old value, including arbitrary tags, bodies, captures and locations. -/
def RuntimeValue.ofCore (value : Core.Value) : RuntimeValue :=
  match value with
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .hostFunction function => .hostFunction function
  | .pair left right => .pair (ofCore left) (ofCore right)
  | .closure parameterType resultType body captured =>
      .coreClosure parameterType resultType body (captured.attach.map (fun value => ofCore value.val))
  | .inLeft rightType payload => .inLeft rightType (ofCore payload)
  | .inRight leftType payload => .inRight leftType (ofCore payload)
  | .cellRef elementType location => .cellRef elementType location
  | .constructed constructor payload => .constructed constructor (ofCore payload)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem value.property
  omega

/-- Project exactly Core-shaped finite data. Every source closure fails, even inside
an unused capture; cell references are copied without dereferencing a store. -/
def RuntimeValue.toCore? (value : RuntimeValue) : Option Core.Value :=
  match value with
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .hostFunction function => some (.hostFunction function)
  | .pair left right => do return .pair (← toCore? left) (← toCore? right)
  | .coreClosure parameterType resultType body captured =>
      (captured.attach.mapM (fun value => toCore? value.val)).map (.closure parameterType resultType body)
  | .inLeft rightType payload => (toCore? payload).map (.inLeft rightType)
  | .inRight leftType payload => (toCore? payload).map (.inRight leftType)
  | .cellRef elementType location => some (.cellRef elementType location)
  | .constructed constructor payload => (toCore? payload).map (.constructed constructor)
  | .sourceClosure _ _ _ _ => none
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem value.property
  omega

end Solcore.Frontend
