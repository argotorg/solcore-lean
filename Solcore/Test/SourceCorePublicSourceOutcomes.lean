import Solcore.Test.SourceCoreMethodOriginEvidenceSourceOutcomes
import Solcore.Test.SourceCoreCanonicalScopedSourceOutcomes
import Solcore.Test.SourceCoreCertifiedLexicalFailureSourceOutcomes

/-! The original public sessions expose their independent Source outcomes and
retain the staged witnesses used by the existing forward fuel conclusions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCorePublicSourceOutcomes

def run : IO Unit := do
  SourceCoreMethodOriginEvidence.SourceOutcomes.run
  SourceCoreCanonicalScoped.SourceOutcomes.run
  SourceCoreCertifiedLexicalFailure.SourceOutcomes.run
  IO.println "PUBLIC_SOURCE_OUTCOMES_PASS: actual X7 at checker1024 and1000; original scoped C6 with retained packed calls; lexical fault and subsequent/fresh identity; exact Dynamic success/fault outcomes, original heaps and forward bounds"

end Tests.SourceCorePublicSourceOutcomes
