import Solcore.Test.SourceCoreSelectedCapturedDirectSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  (shape : Shape header.function.source) (word : Word)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

/-- The actual prior factory result fixes the captured cell. This next-call law
has only a start receipt; the direct call has not executed yet. -/
theorem direct_from_captured (entry : Entry)
    (state : issued.toIssued.State header session [entry])
    (heap : state.heap = capturedHeap word)
    (source : entry.source = .closure (capturedFunction header shape))
    (entryType : entry.sourceType = .function .unit .word)
    (handleType : entry.handle.sourceType = .function .unit .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle .unit fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word word) state.heap ∧
    ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        header.function.context state.heap entry.source [] (.value (.word word)) state.heap ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows header issued.initial
        issued.support.profile recipe [entry] (.word word) checkpoint state.heap) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation []) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry (List.mem_singleton_self _)).2.2
  rw [entryType, source, heap] at typed
  have plain := closure_plain header shape word invocation
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping header).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word word) state.heap := by
    simpa only [source, heap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [entry] header.function.context
      .unit .unit .unit := .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩ ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry
    (List.mem_singleton_self _) entryType input started ready .nil (.word word) rfl handleType ordinary⟩

variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (call : StartedCall session key [.word word] options) (initial : Initial issued.toIssued call)

/-- Factory and direct invocation are related before either public execution is
observed. All sufficiently fueled factory completions expose the exact closure. -/
def ForwardChain (shape : Shape initial.header.function.source) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (state : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧ state.heap = capturedHeap word ∧
          entry.source = .closure (capturedFunction initial.header shape) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle .unit fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              state.heap entry.source [] (.word word) state.heap ∧
            ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
                initial.header.function.context state.heap entry.source [] (.value (.word word)) state.heap ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows initial.header
                issued.initial issued.support.profile recipe [entry] (.word word) checkpoint state.heap) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [])

/-- The lambda captures the original parameter allocation, and the subsequent
ordinary read drives the closed direct public theorem. -/
theorem initial_source_first (shape : Shape initial.header.function.source)
    (resultType : initial.header.function.resultType = .function .unit .word)
    (invocation : Staging.Recursive.Scope) :
    PlainValue initial.header initial.header invocation ⟨[]⟩ [.word word]
      (.closure (capturedFunction initial.header shape)) (capturedHeap word) ∧
    (ForwardChain issued word call initial shape invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.word word]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt invocation word
  have simple : ∀ value ∈ ([.word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word word] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
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
    exact direct_from_captured issued shape word entry state heap source entryType handleType ready accepted invocation
  · exact .inr stopped

/-- The same independent factory trace also determines the whole exported value
and its ordered collection of callable leaves. -/
theorem initial_whole_output (shape : Shape initial.header.function.source)
    (invocation : Staging.Recursive.Scope) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word word]
        (.value (.closure (capturedFunction initial.header shape))) (capturedHeap word) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile recipe [] initial.header.function.resultType call.checkpoint
        (.closure (capturedFunction initial.header shape)) (capturedHeap word)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.word word] := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt invocation word
  have simple : ∀ value ∈ ([.word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word word] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  exact SelectedCompilationStageClosedOutputForward.initial issued call initial simple inputTypes meanings plain

end Tests.SourceCoreSelectedCapturedDirect
