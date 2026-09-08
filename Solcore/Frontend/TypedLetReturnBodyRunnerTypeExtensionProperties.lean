import Solcore.Frontend.TypedLetReturnBodyTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyRunner

/-! Meaning extension preserves successful complete body results. Mutual
extension also retains rejection; actual inputs, fuel and store stay fixed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnBody?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} (extension : TypeNameTable.Extends old new)
    (accepted : inputs.checkTypedLetReturnBody? old owner body = some (core, type)) :
    inputs.checkTypedLetReturnBody? new owner body = some (core, type) :=
  elaborateTypedLetReturnBody?_some_of_extends extension accepted

theorem checkTypedLetReturnBody?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (body : Syntax.Block) :
    inputs.checkTypedLetReturnBody? old owner body = inputs.checkTypedLetReturnBody? new owner body :=
  elaborateTypedLetReturnBody?_eq_of_mutual_extends forward backward owner inputs.toTypeInputs body

/-- The whole successful pair is retained, even at insufficient fuel with a
genuine suspended state. No separate typing or sufficient-fuel premise is used. -/
theorem runTypedLetReturnBody?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : inputs.runTypedLetReturnBody? old owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnBody? new owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnBody? old owner body with
  | none => simp [runTypedLetReturnBody?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved := checkTypedLetReturnBody?_some_of_extends extension checked
      simpa only [runTypedLetReturnBody?, checked, preserved] using accepted

theorem runTypedLetReturnBody?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    inputs.runTypedLetReturnBody? old owner fuel body store =
      inputs.runTypedLetReturnBody? new owner fuel body store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?_eq_of_mutual_extends
    inputs forward backward owner body]

end Solcore.Frontend.LocalInputs
