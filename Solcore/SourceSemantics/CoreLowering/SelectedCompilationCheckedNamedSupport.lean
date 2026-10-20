import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport

/-! The authentic check receipt, selected bodies and existing replacement
ranges supply both facets consumed by named execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry

theorem Certificate.namedSupport {compiled : Frontend.SourceCoreUnifiedCompilation.Compiled}
    (certificate : Certificate compiled) : SelectedCompilationNamedSupport.Support compiled :=
  ⟨certificate.bodyTyping, certificate.registryBodies⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
