import Solcore.Frontend.TypedLetReturnTreeTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnTreeRunner

/-! Meaning extension preserves successful complete recursive-body results.
Mutual extension retains rejection too; actual inputs, fuel and store stay fixed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnTree?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} (extension : TypeNameTable.Extends old new)
    (accepted : inputs.checkTypedLetReturnTree? old owner body = some (core, type)) :
    inputs.checkTypedLetReturnTree? new owner body = some (core, type) :=
  elaborateTypedLetReturnTree?_some_of_extends extension accepted

theorem checkTypedLetReturnTree?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (body : Syntax.Block) :
    inputs.checkTypedLetReturnTree? old owner body = inputs.checkTypedLetReturnTree? new owner body :=
  elaborateTypedLetReturnTree?_eq_of_mutual_extends forward backward owner inputs.toTypeInputs body

/-- Preserve the full successful pair, including a genuine suspended state at
insufficient fuel. No extra typing or sufficient-fuel premise is introduced. -/
theorem runTypedLetReturnTree?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : inputs.runTypedLetReturnTree? old owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? new owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnTree? old owner body with
  | none => simp [runTypedLetReturnTree?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved := checkTypedLetReturnTree?_some_of_extends extension checked
      simpa only [runTypedLetReturnTree?, checked, preserved] using accepted

theorem runTypedLetReturnTree?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    inputs.runTypedLetReturnTree? old owner fuel body store =
      inputs.runTypedLetReturnTree? new owner fuel body store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?_eq_of_mutual_extends
    inputs forward backward owner body]

end Solcore.Frontend.LocalInputs
