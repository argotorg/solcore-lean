import Solcore.Test.SourceCoreConstructorCallsPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectOutputForward

/-! Independent Source success also implies public nominal-constructor export and ordered
nested collection for every sufficient execution and output fuel budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

def SelectedAt {fixture : CompiledFixture} {publicArtifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion publicArtifact)
    (selection : Selection (containerType fixture.dataType) completion.value) (source : Dynamic.Value)
    (outputFuel : Nat) (added : List Entry) : Prop :=
  ∃ (artifact : SourceCoreIndexedSession.Artifact) (actual : SourceCoreIndexedSession.Completion artifact)
    (native : Core.Value) (type : Core.Ty), completion.IndexedAt actual ∧
    Selected fixture.recipe.compiled.compatible.checked actual.session selection source native type outputFuel added

def ForwardCollectionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint artifact,
    session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion artifact,
          outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
          ∀ selection : Selection (containerType fixture.dataType) completion.value,
            ∃ (added : List Entry) (next : RetainedState support completion.session (entries ++ added)),
              next.heap = after ∧ added.map Entry.handle = selection.handles ∧
              SelectedAt (fixture := fixture) completion selection source outputFuel added

theorem SequenceWitness.forward_collection {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    ForwardCollectionAt meaning.support sequence.named.completion.session
      [meaning.first, meaning.factory, meaning.builtin, meaning.named]
      sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
      meaning.source meaning.collectedState.heap := by
  let state := meaning.issuedState
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have factoryReady := sequence.factory.issued.exportsReady firstReady
  have builtinReady := sequence.builtin.issued.exportsReady factoryReady
  have exportsReady := sequence.named.issued.exportsReady builtinReady
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := sequence.construction.executed
  have member : meaning.named ∈ [meaning.first, meaning.factory, meaning.builtin, meaning.named] := by simp
  have input := construction_input
    (entries := [meaning.first, meaning.factory, meaning.builtin, meaning.named])
    (context := meaning.support.makeHeader.header.function.context)
    meaning.factory meaning.first meaning.builtin (by simp) (by simp) (by simp)
    meaning.factoryType meaning.firstType meaning.builtinType meaning.factoryHandle meaning.firstHandle meaning.builtinHandle
  obtain ⟨sources, size, packing, trace⟩ := meaning.constructionTrace
  refine ⟨publicCheckpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectOutputForward.forward_call meaning.support.program
    fixture.recipePrepared state meaning.named member meaning.namedType input
    (by simpa only [meaning.namedHandle] using accepted) exportsReady packing trace


def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning : ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver,
        ForwardCollectionAt meaning.support sequence.named.completion.session
          [meaning.first, meaning.factory, meaning.builtin, meaning.named]
          sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
          meaning.source meaning.collectedState.heap := by
    obtain ⟨receiver, witness⟩ := closed_sequence_meaning fixture observed extra admission makeStages readStages sequence
    obtain ⟨witness⟩ := witness
    exact ⟨receiver, witness, witness.forward_collection⟩
  IO.println "Constructor recursive child and payload collection: independent Source meaning, sufficient public fuel, retained callable reuse20/30export/10/37 proved"

end Tests.SourceCoreConstructorCalls
