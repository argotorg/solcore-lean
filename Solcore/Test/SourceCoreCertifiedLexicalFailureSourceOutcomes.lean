import Solcore.Test.SourceCoreCertifiedLexicalFailurePublicExecution
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes

/-! The original failed call and both identity calls have independent Dynamic
outcomes at the exact heaps returned by the authentic public reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCertifiedLexicalFailure.SourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CertifiedPublicSession (Issued)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}

theorem first_fault {stages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} (meaning : FirstMeaning issued stages first) :
    PlainFault meaning.initial.header meaning.initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.initial.header.function)
      ⟨[]⟩ [] (.uninitializedLocation meaning.location) meaning.after.heap :=
  meaning.trace.semanticFault_plain

theorem continuation_value {failedStages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} {before : FirstMeaning issued failedStages first}
    {stages : ObservedStages fixture observed.identityRow}
    {next : ObservedContinuation (original_first first)}
    (meaning : ContinuationMeaning before stages next) :
    PlainValue before.initial.header meaning.request.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.request.header.function)
      before.after.heap [.word seed] (.word seed) meaning.after.heap := meaning.trace.value_plain

theorem fresh_value {stages : ObservedStages fixture observed.identityRow}
    {fresh : FreshIdentity fixture observed} (meaning : FreshMeaning issued stages fresh) :
    PlainValue meaning.initial.header meaning.initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.initial.header.function)
      ⟨[]⟩ [.word seed] (.word seed) meaning.after.heap := meaning.trace.value_plain

/-- The same witnesses retain the absent cell, its survival after continuation,
empty handle histories, actual diagnostics and all three forward fuel bounds. -/
theorem closed_outcomes (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedCertificate fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (first : First fixture observed)
    (next : ObservedContinuation (original_first first))
    (fresh : FreshIdentity fixture observed) :
    ∃ (issued : Issued fixture.recipe) (before : FirstMeaning issued failedStages first)
      (after : ContinuationMeaning before identityStages next)
      (freshIssued : Issued fixture.recipe) (freshMeaning : FreshMeaning freshIssued identityStages fresh),
      PlainFault before.initial.header before.initial.header
        (RecursiveStageRegistry.scope failedStages.sidecar [] before.initial.header.function)
        ⟨[]⟩ [] (.uninitializedLocation before.location) before.after.heap ∧
      PlainValue before.initial.header after.request.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] after.request.header.function)
        before.after.heap [.word seed] (.word seed) after.after.heap ∧
      PlainValue freshMeaning.initial.header freshMeaning.initial.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] freshMeaning.initial.header.function)
        ⟨[]⟩ [.word seed] (.word seed) freshMeaning.after.heap := by
  obtain ⟨issued, before, ⟨after⟩, freshIssued, ⟨freshMeaning⟩⟩ :=
    SourceCoreCertifiedLexicalFailure.closed_outcomes fixture observed admission failedStages identityStages first next fresh
  exact ⟨issued, before, after, freshIssued, freshMeaning,
    first_fault before, continuation_value after, fresh_value freshMeaning⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeCertificate fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let first ← Tests.SourceCoreDirectFailure.observePublicRun fixture observed
  let next ← observeContinuation (original_first first)
  let fresh ← observeFreshIdentity fixture observed
  have _outcomes := closed_outcomes fixture observed admission failedStages identityStages first next fresh
  IO.println "LEXICAL_SOURCE_OUTCOMES_PASS: original checker1000/compiler100; independent Dynamic uninitialized-location fault retains its allocated absent cell; same session identity37 preserves it; fresh identity37; exact named dictionaries, empty handle histories and all three forward bounds"

end Tests.SourceCoreCertifiedLexicalFailure.SourceOutcomes
