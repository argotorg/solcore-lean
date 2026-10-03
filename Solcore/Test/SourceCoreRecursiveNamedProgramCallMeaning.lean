import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning

/-! Formal consumers keep the actual caller layout, argument bundle receipt
and independent source entry conditions for emitted native calls. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramCallMeaning
open Solcore.SourceSemantics.CoreLowering
abbrev emitted_call_has_sufficient_fuel :=
  @RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel
abbrev completed_call_reflects_program :=
  @RecursiveNamedProgramCallMeaning.completed_call_reflects_program
end Tests.SourceCoreRecursiveNamedProgramCallMeaning
