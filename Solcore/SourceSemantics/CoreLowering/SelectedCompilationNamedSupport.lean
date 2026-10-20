import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation

/-! Named execution consumes original selected body typing and preservation for
its actual prepared registry. The legacy whole-program API is an adapter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
open Core Frontend SourceInference

structure Support (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  bodyTyping : SelectedCompilationBodyTyping.Bodies compiled
  registryBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)

theorem Support.of_program {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) : Support compiled :=
  ⟨.of_program wellFormed, .of_program wellFormed⟩

theorem Support.certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    (support : Support compiled)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    SelectedCompilationNamedSourceTyping.Certified header :=
  SelectedCompilationHeaderCertificates.certified support.bodyTyping header

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
