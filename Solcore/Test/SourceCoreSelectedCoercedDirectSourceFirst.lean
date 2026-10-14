import Solcore.Test.SourceCoreSelectedCoercedDirectMeaning
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable (fixture : Fixture) (issued : Profiled fixture.recipe)
  {keepHeader : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader)
  {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available header) (flag : Bool)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

/-- The actual prior factory result fixes the captured cell. This next-call law
has only a start receipt; the direct call has not executed yet. -/
theorem direct_from_captured (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader) (entry : Entry)
    (state : issued.toIssued.State header session [entry])
    (heap : state.heap = capturedHeap flag)
    (source : entry.source = .closure (capturedFunction header (fixture.shapeAt makeFacts)))
    (entryType : entry.sourceType = .function .unit .word)
    (handleType : entry.handle.sourceType = .function .unit .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle .unit fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) ∧
    ((Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation
        header.function.context state.heap entry.source [] (.value (.word (converted flag))) (convertedHeap flag) ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows header issued.initial
        issued.support.profile fixture.recipe [entry] (.word (converted flag)) checkpoint (convertedHeap flag)) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation []) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry (List.mem_singleton_self _)).2.2
  rw [entryType, source, heap] at typed
  have plain := fixture.closure_plain issued makeFacts keepFacts invocation flag
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping header).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) := by
    simpa only [source, heap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [entry] header.function.context
      .unit .unit .unit := .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩ ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry
    (List.mem_singleton_self _) entryType input started ready .nil (.word (converted flag)) rfl handleType ordinary⟩

variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (call : StartedCall session key [.bool flag] options) (initial : Initial issued.toIssued call)

/-- Factory and direct invocation are related before either public execution is
observed. All sufficiently fueled factory completions expose the exact closure. -/
def ForwardChain (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (state : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧ state.heap = capturedHeap flag ∧
          entry.source = .closure (capturedFunction initial.header (fixture.shapeAt makeFacts)) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle .unit fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) ∧
            ((Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation
                initial.header.function.context state.heap entry.source [] (.value (.word (converted flag))) (convertedHeap flag) ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows initial.header
                issued.initial issued.support.profile fixture.recipe [entry] (.word (converted flag)) checkpoint (convertedHeap flag)) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [])

/-- The lambda captures the original parameter allocation, and the subsequent
ordinary read drives the closed direct public theorem. -/
theorem initial_source_first (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader) (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header)
    (resultType : initial.header.function.resultType = .function .unit .word)
    (invocation : Staging.Recursive.Scope) :
    PlainValue initial.header initial.header invocation ⟨[]⟩ [.bool flag]
      (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag) ∧
    (ForwardChain fixture issued flag call initial makeFacts invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.bool flag]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header (fixture.shapeAt makeFacts) sourceAt invocation flag
  have simple : ∀ value ∈ ([.bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .bool _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.bool flag] initial.header.types := by
    rw [input_types initial.header (fixture.shapeAt makeFacts)]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have forward := SelectedCompilationStageClosedInitialForward.function issued call initial simple inputTypes meanings
    (by rw [resultType]; rfl) plain
  refine ⟨plain, ?_⟩
  rcases forward with ⟨_source, requiredExecution, requiredOutput, forward⟩ | stopped
  · left
    refine ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, ready, entry, entryType, source, returned, handleType, state, heap⟩ :=
      forward executionFuel outputFuel outcome executionBound outputBound resumed
    rw [resultType] at entryType handleType
    refine ⟨completion, actual, entry, state, returned, heap, source, ?_⟩
    intro fuel checkpoint accepted
    exact direct_from_captured fixture issued makeFacts flag (keepFacts := keepFacts) entry state heap source entryType handleType ready accepted invocation
  · exact .inr stopped

/-- The same independent factory trace also determines the whole exported value
and its ordered collection of callable leaves. -/
theorem initial_whole_output (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header)
    (invocation : Staging.Recursive.Scope) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.bool flag]
        (.value (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts)))) (capturedHeap flag) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType call.checkpoint
        (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.bool flag] := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header (fixture.shapeAt makeFacts) sourceAt invocation flag
  have simple : ∀ value ∈ ([.bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .bool _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.bool flag] initial.header.types := by
    rw [input_types initial.header (fixture.shapeAt makeFacts)]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  exact SelectedCompilationStageClosedOutputForward.initial issued call initial simple inputTypes meanings plain

end Tests.SourceCoreSelectedCoercedDirect
