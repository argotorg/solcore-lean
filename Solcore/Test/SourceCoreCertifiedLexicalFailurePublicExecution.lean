import Solcore.Test.SourceCoreCertifiedLexicalFailureMeaning

/-! The original lexical failure and identity declarations now consume the
whole-program certificate and automatic catalog for their public conclusions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

/-- Actual failure, continuation and fresh scalar success retain their original
Source heaps, with sufficient-fuel conclusions at each actual checkpoint. -/
theorem closed_outcomes (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedCertificate fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (first : First fixture observed)
    (next : ObservedContinuation (original_first first))
    (fresh : FreshIdentity fixture observed) :
    ∃ issued : CertifiedPublicSession.Issued fixture.recipe,
      ∃ before : FirstMeaning issued failedStages first,
        Nonempty (ContinuationMeaning before identityStages next) ∧
        ∃ freshIssued : CertifiedPublicSession.Issued fixture.recipe,
          Nonempty (FreshMeaning freshIssued identityStages fresh) := by
  obtain ⟨issued, ⟨before⟩⟩ := first_meaning admission failedStages first
  exact ⟨issued, before, continuation_meaning before identityStages next,
    fresh_meaning admission identityStages fresh⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeCertificate fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let first ← Tests.SourceCoreDirectFailure.observePublicRun fixture observed
  let next ← observeContinuation (original_first first)
  let fresh ← observeFreshIdentity fixture observed
  have _meaning := closed_outcomes fixture observed admission failedStages identityStages first next fresh
  IO.println "CERTIFIED_SESSION_OUTCOMES_PASS: original checker1000/compiler100; first uninitialized fault retains absent cell; same session identity(37) preserves it; fresh identity(37); automatic catalog, empty handle histories and all three forward bounds"

end Tests.SourceCoreCertifiedLexicalFailure
