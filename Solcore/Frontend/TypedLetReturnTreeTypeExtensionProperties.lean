import Solcore.Frontend.TypedLetReturnTreeElaboration
import Solcore.Frontend.StructuralTypeTableProperties

/-! Preserve annotation meanings throughout recursive bodies without changing
source, owner, inputs or exact Core. Both arms retain their original scope. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnTreeElaborates new owner inputs body core type := by
  induction elaboration with
  | single child => exact .single child
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding (meaning.extend_types extension) unused resolution lowered typing ih
  | inferred unused resolution lowered typing _ ih =>
      exact .inferred unused resolution lowered typing ih
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional resolution lowered typing thenIH elseIH

theorem TypedLetReturnTreeHasType.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnTreeHasType new owner inputs body type := by
  induction typing with
  | single child => exact .single child
  | binding meaning unused initializer _ ih =>
      exact .binding (meaning.extend_types extension) unused initializer ih
  | inferred unused initializer _ ih => exact .inferred unused initializer ih
  | conditional condition _ _ thenIH elseIH =>
      exact .conditional condition thenIH elseIH

theorem elaborateTypedLetReturnTree?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateTypedLetReturnTree? old owner inputs body = some (core, type)) :
    elaborateTypedLetReturnTree? new owner inputs body = some (core, type) :=
  ((elaborateTypedLetReturnTree?_elaborates accepted).extend_types extension).complete

/-- Mutual first-match preservation retains every optional result, including
rejection. One-way extension alone can repair an unknown annotation in either arm. -/
theorem elaborateTypedLetReturnTree?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? old owner inputs body =
      elaborateTypedLetReturnTree? new owner inputs body := by
  cases oldResult : elaborateTypedLetReturnTree? old owner inputs body with
  | none =>
      cases newResult : elaborateTypedLetReturnTree? new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateTypedLetReturnTree?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateTypedLetReturnTree?_some_of_extends forward oldResult).symm

end Solcore.Frontend
