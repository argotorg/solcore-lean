import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeParameterDeclarations

/-! Meaning-preserving table extension retains exact static declarations,
including arbitrary initial inputs and every generated identity. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Only annotation evidence changes; the same types drive the same identity
allocation, and the original initial and final bundles remain untouched. -/
theorem RuntimeParametersDeclareFrom.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial final : LocalTypeInputs}
    {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom old owner initial parameters final)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersDeclareFrom new owner initial parameters final := by
  induction declared with
  | nil => exact .nil
  | cons meaning unused _ ih => exact .cons (meaning.extend_types extension) unused ih

theorem RuntimeParametersDeclare.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare old owner parameters inputs)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersDeclare new owner parameters inputs :=
  RuntimeParametersDeclareFrom.extend_types declared extension

theorem declareRuntimeParameters?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (extension : TypeNameTable.Extends old new)
    (accepted : declareRuntimeParameters? old owner parameters = some inputs) :
    declareRuntimeParameters? new owner parameters = some inputs :=
  (RuntimeParametersDeclare.extend_types (declareRuntimeParameters?_sound accepted) extension).complete

/-- Mutual preservation includes rejection. One-way extension alone may make
a previously unknown annotation available and turn rejection into success. -/
theorem declareRuntimeParameters?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (parameters : List Syntax.FunctionParameter) :
    declareRuntimeParameters? old owner parameters = declareRuntimeParameters? new owner parameters := by
  cases oldResult : declareRuntimeParameters? old owner parameters with
  | none =>
      cases newResult : declareRuntimeParameters? new owner parameters with
      | none => rfl
      | some inputs =>
          have preserved := declareRuntimeParameters?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some inputs => exact (declareRuntimeParameters?_some_of_extends forward oldResult).symm

end Solcore.Frontend
