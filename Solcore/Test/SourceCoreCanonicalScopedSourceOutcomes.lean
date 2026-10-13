import Solcore.Test.SourceCoreCanonicalScopedCompilerProfile
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes

/-! Independent Dynamic outcomes for the original six-call scoped closure
session, including all three packed calls on retained captured closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.SourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CompilerProfile
open CertifiedPublicSession (Issued)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

/-- The original packing, arity and retained entry remain in the indexed
meaning; this projection preserves its exact arguments and before/after heaps. -/
def DirectValue
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {before : issued.State anchor session entries} {entry : RecursiveNamedPublicFunctionHistory.Entry}
    {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope) : Prop :=
  Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context scope.evidence (Staging.Recursive.callableEvidence entry.source)
    before.heap entry.source meaning.arguments (.word word) meaning.after.heap

theorem direct_value
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {before : issued.State anchor session entries} {entry : RecursiveNamedPublicFunctionHistory.Entry}
    {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope) : DirectValue meaning :=
  meaning.trace.sound.value_plain

structure DynamicMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  second : PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.second.request.header.function)
    meaning.first.after.heap [.word secondSeed] meaning.second.entry.source meaning.second.after.heap
  firstRead : DirectValue meaning.firstRead
  intervening : PlainValue meaning.first.initial.header meaning.intervening.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.intervening.request.header.function)
    meaning.firstRead.after.heap [.word interveningSeed] meaning.intervening.entry.source meaning.intervening.after.heap
  secondRead : DirectValue meaning.secondRead
  repeatedRead : DirectValue meaning.repeatedRead

theorem dynamic_meaning (meaning : SequenceMeaning issued stages sequence) : DynamicMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, direct_value meaning.firstRead,
    meaning.intervening.trace.value_plain, direct_value meaning.secondRead, direct_value meaning.repeatedRead⟩

theorem closed_outcomes (profile : CompilerProfile.Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      DynamicMeaning meaning ∧ meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      CompilerProfile.ForwardMeaning meaning := by
  obtain ⟨issued, meaning, distinct, forward⟩ := CompilerProfile.closed_sequence_forward_meaning profile stages sequence
  exact ⟨issued, meaning, dynamic_meaning meaning, distinct, forward⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← CompilerProfile.observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _outcomes := closed_outcomes profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.value.table.rows.length == 3 do
    throw (IO.userError "scoped source outcomes changed original cache3/table3")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.intervening.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize]
  unless stores == [4,7,10,44,47,81,106] do
    throw (IO.userError s!"scoped source outcomes changed original stores: {reprStr stores}")
  IO.println "SCOPED_SOURCE_OUTCOMES_PASS: original C6 at checker1000; six independent Dynamic applications; three exact packed retained-closure calls; make10/make20/A10/make30/B20/A11; captured values, reached heaps and all six forward bounds"

end Tests.SourceCoreCanonicalScoped.SourceOutcomes
