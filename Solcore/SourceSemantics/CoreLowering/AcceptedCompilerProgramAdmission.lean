import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission

/-! Whole-program clients reuse the selected compilation producer. Their
existing validity receipt supplies the selected body facts internally. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerProgramAdmission
open Core Frontend SourceInference
open CompilerProgramStaticProfile
open CallableIndexedOwnedPreparedProgramAdmission (Certificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Actual indices retain the complete original named carrier. -/
theorem profile_at {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (profile : StaticProfile compiled) (selected : compiled.indexed.base.functions[index]? = some named) :
    Nonempty (Row compiled named profile.table.rows) :=
  SelectedCompilationProgramAdmission.profile_at profile selected

/-- The existing full-program interface uses the same compiler certificate
producer, including its original dictionary and closed coercion alternatives. -/
theorem of_profile (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : StaticProfile compiled) : Nonempty (Certificate compiled) :=
  SelectedCompilationProgramAdmission.of_profile checked
    (SelectedCompilationBodyTyping.Bodies.of_program wellFormed) profile

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerProgramAdmission
