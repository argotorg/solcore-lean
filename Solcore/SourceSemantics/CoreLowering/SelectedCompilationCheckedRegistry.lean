import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession

/-! Checked selected bodies and the complete actual substitution ranges issue
preservation for the unchanged registry. This also covers generalized local
bodies outside the older whole-cache static profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
open Core Frontend SourceInference

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  checked : ∃ raw checkingFuel, checkProgram raw checkingFuel = .ok compiled.sourceProgram
  bodyTyping : SelectedCompilationBodyTyping.Bodies compiled
  ranges : SelectedCompilationRegistryMethodCertificates.Ranges compiled

theorem Certificate.registryBodies {compiled : SourceCoreUnifiedCompilation.Compiled}
    (certificate : Certificate compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled) := by
  obtain ⟨raw, fuel, checked⟩ := certificate.checked
  exact SelectedCompilationRegistryBodies.of_checked
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
    certificate.bodyTyping checked certificate.ranges

theorem of_checked {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
    (ranges : SelectedCompilationRegistryMethodCertificates.Ranges compiled) : Certificate compiled :=
  ⟨⟨raw,checkingFuel,checked⟩,bodyTyping,ranges⟩

theorem of_profiled {recipe : SourceCoreIndexedSession.Recipe}
    (issued : SelectedCompilationCertifiedPublicSession.Profiled recipe) : Certificate recipe.compiled :=
  ⟨issued.checked, issued.support.bodyTyping,
    SelectedCompilationRegistryMethodCertificates.ranges_of_profile issued.staticProfile⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
