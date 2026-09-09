import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeParametersProperties

/-! Preserve the complete actual binding, not just its value-free projection.
Only annotation evidence changes; original values and generated IDs do not. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Arbitrary initial rows, including repeated spellings, remain exactly the
same. The original arguments supply all types, values and typing evidence. -/
theorem RuntimeParametersBindFrom.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial final : LocalInputs}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom old owner initial parameters arguments final)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersBindFrom new owner initial parameters arguments final := by
  induction bound with
  | nil => exact .nil
  | cons meaning unused _ ih => exact .cons (meaning.extend_types extension) unused ih

theorem RuntimeParametersBind.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind old owner parameters arguments inputs)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersBind new owner parameters arguments inputs :=
  RuntimeParametersBindFrom.extend_types bound extension

theorem bindRuntimeParameters?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (extension : TypeNameTable.Extends old new)
    (accepted : bindRuntimeParameters? old owner parameters arguments = some inputs) :
    bindRuntimeParameters? new owner parameters arguments = some inputs :=
  (RuntimeParametersBind.extend_types (bindRuntimeParameters?_sound accepted) extension).complete

/-- Mutual extension retains rejection as well as every actual output row.
One-way extension can supply an unknown annotation and enable binding. -/
theorem bindRuntimeParameters?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) :
    bindRuntimeParameters? old owner parameters arguments =
      bindRuntimeParameters? new owner parameters arguments := by
  cases oldResult : bindRuntimeParameters? old owner parameters arguments with
  | none =>
      cases newResult : bindRuntimeParameters? new owner parameters arguments with
      | none => rfl
      | some inputs =>
          have preserved := bindRuntimeParameters?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some inputs => exact (bindRuntimeParameters?_some_of_extends forward oldResult).symm

end Solcore.Frontend
