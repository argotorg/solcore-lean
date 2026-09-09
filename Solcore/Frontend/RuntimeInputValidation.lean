import Solcore.Frontend.RuntimeParameters

/-! Opt-in checking of actual argument references and every cell in one supplied
world. Structural argument evidence already validates closure bodies/captures;
this is not a validator for unproved raw values or an automatic entry guard. -/

set_option autoImplicit false

namespace Solcore.Frontend

mutual
  private def valueReferencesValid (world : Core.StoreTyping) : Core.Value → Bool
    | .unit | .bool _ | .word _ => true
    | .hostFunction _ => false
    | .pair left right => valueReferencesValid world left && valueReferencesValid world right
    | .closure _ _ _ captured => environmentReferencesValid world captured
    | .inLeft _ payload | .inRight _ payload | .constructed _ payload => valueReferencesValid world payload
    | .cellRef type location => decide (world[location]? = some type)
  termination_by value => sizeOf value

  private def environmentReferencesValid (world : Core.StoreTyping) : Core.Environment → Bool
    | [] => true
    | value :: rest => valueReferencesValid world value && environmentReferencesValid world rest
  termination_by environment => sizeOf environment
end

private def storeValid : Core.StoreTyping → Core.Store → Bool
  | [], [] => true
  | type :: types, value :: values =>
      type.isCellPayload && decide (value.type = type) && storeValid types values
  | _, _ => false

/-- Validate runtime premises for the existing structurally typed arguments and
the whole supplied store, without changing either input or inferring a world. -/
def validateRuntimeInputs (world : Core.StoreTyping) (arguments : List TypedRuntimeArgument)
    (store : Core.Store) : Bool :=
  arguments.all (fun argument => valueReferencesValid world argument.value) && storeValid world store

end Solcore.Frontend
