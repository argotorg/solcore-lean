import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.TypeNameTableExtensionProperties

/-! Preserve annotation meanings without changing source, inputs or exact Core.
One-way extension preserves success; mutual extension also preserves rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnBodyElaborates new owner inputs body core type := by
  induction elaboration with
  | terminal child => exact .terminal child
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding (meaning.extend_types extension) unused resolution lowered typing ih

theorem TypedLetReturnBodyHasType.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnBodyHasType new owner inputs body type := by
  induction typing with
  | terminal child => exact .terminal child
  | binding meaning unused initializer _ ih =>
      exact .binding (meaning.extend_types extension) unused initializer ih

theorem elaborateTypedLetReturnBody?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateTypedLetReturnBody? old owner inputs body = some (core, type)) :
    elaborateTypedLetReturnBody? new owner inputs body = some (core, type) :=
  ((elaborateTypedLetReturnBody?_elaborates accepted).extend_types extension).complete

/-- Mutual first-match preservation retains the full optional result without
equating tables or requiring unique keys. One-way extension can repair rejection. -/
theorem elaborateTypedLetReturnBody?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnBody? old owner inputs body =
      elaborateTypedLetReturnBody? new owner inputs body := by
  cases oldResult : elaborateTypedLetReturnBody? old owner inputs body with
  | none =>
      cases newResult : elaborateTypedLetReturnBody? new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateTypedLetReturnBody?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateTypedLetReturnBody?_some_of_extends forward oldResult).symm

end Solcore.Frontend
