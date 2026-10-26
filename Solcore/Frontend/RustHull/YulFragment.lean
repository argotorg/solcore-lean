import Solcore.Frontend.RustHull.Syntax

/-! The inline Yul the common recursive proof accepts: an assembly block of one
statement that calls a supported name on two literals. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulFragment

def Eligible (supported : String → Prop) : List YulStmt → Prop
  | [⟨.expression ⟨.call name [⟨.literal _, _⟩, ⟨.literal _, _⟩], _⟩, _⟩] => supported name.name
  | _ => False

theorem Eligible.empty {body : List YulStmt} (eligible : Eligible (fun _ => False) body) : False := by
  unfold Eligible at eligible
  split at eligible <;> exact eligible

end Solcore.Frontend.RustHull.YulFragment
