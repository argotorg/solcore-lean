import Solcore.Test.SourceCoreInitialLexicalFailureFixture
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionOutcomes

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

structure ObservedCertificate (fixture : CompiledFixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate

def observeCertificate (fixture : CompiledFixture) : IO (ObservedCertificate fixture) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original lexical program certificate rejected")
  | some certificate => return ⟨certificate, accepted⟩

def probeCertificate : IO Unit := do
  let fixture ← compiledFixture
  let _certificate ← observeCertificate fixture
  IO.println "CERTIFIED_LEXICAL_PROGRAM_PASS: original checker1000/compiler100; complete certificate64"

end Tests.SourceCoreCertifiedLexicalFailure
