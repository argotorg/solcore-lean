import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource

/-! Formal consumers retain the complete public program-entry and native
completion signatures, including their independent entry conditions. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramEntrySource
open Solcore.SourceSemantics.CoreLowering

abbrev program_has_sufficient_native_fuel :=
  @RecursiveNamedProgramEntrySource.program_has_sufficient_native_fuel

abbrev native_success_reflects_program :=
  @RecursiveNamedProgramEntrySource.native_success_reflects_program

end Tests.SourceCoreRecursiveNamedProgramEntrySource
