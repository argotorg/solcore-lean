import Solcore.Frontend.RuntimeFunctionHeaderTypeExtensionProperties
import Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.TypedLetReturnBodyTypeExtensionProperties

/-! Extending caller meanings preserves the complete compiled record. Exact
body provenance is retained without introducing or supplying runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles old owner declaration compiled)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionCompiles new owner declaration compiled :=
  ⟨compilation.header.extend_types extension,
    RuntimeParametersDeclare.extend_types compilation.parameters extension,
    compilation.body.extend_types extension⟩

theorem compileRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (extension : TypeNameTable.Extends old new)
    (accepted : compileRuntimeFunction? old owner declaration = some compiled) :
    compileRuntimeFunction? new owner declaration = some compiled :=
  ((compileRuntimeFunction?_sound accepted).extend_types extension).complete

/-- Both directions preserve failure as well as the exact static rows, open
Core and result type. No equality of the caller tables themselves is required. -/
theorem compileRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl) :
    compileRuntimeFunction? old owner declaration = compileRuntimeFunction? new owner declaration := by
  cases oldResult : compileRuntimeFunction? old owner declaration with
  | none =>
      cases newResult : compileRuntimeFunction? new owner declaration with
      | none => rfl
      | some compiled =>
          have preserved := compileRuntimeFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some compiled => exact (compileRuntimeFunction?_some_of_extends forward oldResult).symm

end Solcore.Frontend
