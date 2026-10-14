import Solcore.Test.SourceCoreCertifiedLexicalFailureRuntime
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionSourceFailures
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionOutcomes

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

def observeProfile (fixture : CompiledFixture) :
    IO (CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled) := do
  have checked : checkProgram _ _ = .ok fixture.recipe.compiled.sourceProgram := by
    rw [fixture.sameProgram]
    exact fixture.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile fixture.recipe.compiled checked
    | throw (IO.userError "selected lexical profile rejected")
  pure profile

end Tests.SourceCoreSelectedLexicalFailure
