import Solcore.Test.SourceCoreMethodOriginEvidenceFixture
import Solcore.Frontend.ProgramCheckingFuelAgreement

/-! The companion check retains the same complete original program at fuel
1000. Its original successful receipt is kept for public support issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics

structure OriginalCheckAt1000 (fixture : CompiledFixture) : Prop where
  accepted : checkProgram workspace 1000 = .ok fixture.program
  nonemptyMethods : fixture.program.methods.length = 1

def observeOriginalCheckAt1000 (fixture : CompiledFixture) : IO (PLift (OriginalCheckAt1000 fixture)) := do
  match accepted : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    have same := checkProgram_success_unique_fuel accepted fixture.checked
    pure ⟨⟨by simpa only [same] using accepted, fixture.methodCount⟩⟩

end Tests.SourceCoreMethodOriginEvidence
