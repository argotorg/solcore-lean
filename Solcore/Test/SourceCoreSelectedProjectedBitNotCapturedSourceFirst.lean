import Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedFixture
import Solcore.Test.SourceCoreSelectedProjectedBitNotSourceFirst
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicInitialData

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot.Captured
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  (shape : Shape header.function.source) (before : Dynamic.Heap)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (entry : Entry)
  (state : issued.toIssued.State anchor session entries)

/-- A current ordinary call is constructed before its public completion. The
only closure typing used here comes from the genuine retained session history. -/
theorem direct_from_captured (member : entry ∈ entries)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value)) (suffix : List Dynamic.Cell)
    (sameHeap : state.heap = heap before ((.word key, .word previous) :: tail) suffix)
    (source : entry.source = .closure (function header shape before))
    (entryType : entry.sourceType = .function .word .word)
    (handleType : entry.handle.sourceType = .function .word .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle (.word key) fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous.bitNot) :: tail) (suffix ++ [keyCell key])) ∧
    ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        anchor.function.context state.heap entry.source [.word key] (.value (.word previous.bitNot))
        (heap before ((.word key, .word previous.bitNot) :: tail) (suffix ++ [keyCell key])) ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
        issued.support.profile recipe entries (.word previous.bitNot) checkpoint
        (heap before ((.word key, .word previous.bitNot) :: tail) (suffix ++ [keyCell key]))) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [.word key]) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry member).2.2
  rw [entryType, source, sameHeap] at typed
  have plain := closure_plain header shape before key previous tail suffix invocation
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping anchor).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous.bitNot) :: tail) (suffix ++ [keyCell key])) := by
    simpa only [source, sameHeap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      .word (.word key) (.word key) :=
    .data ⟨.word key, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word key⟩
      ⟨.word key, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word key⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry member
    entryType input started ready (.singleton _) (.word previous.bitNot) rfl handleType ordinary⟩

/-- Every sufficiently fueled first completion retains the same handle and
captured location. The second ordinary call restores the mapping's first entry
and appends a second argument cell, before the second public call executes. -/
def RestoreAfterFirst (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value))
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word previous.bitNot ∧
        ∃ next : issued.toIssued.State anchor completion.session entries,
          next.heap = heap before ((.word key, .word previous.bitNot) :: tail) [keyCell key] ∧
          ∀ nextFuel (second : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle (.word key) nextFuel = .ok second →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              next.heap entry.source [.word key] (.word previous)
              (heap before ((.word key, .word previous) :: tail) [keyCell key, keyCell key]) ∧
            ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
                anchor.function.context next.heap entry.source [.word key] (.value (.word previous))
                (heap before ((.word key, .word previous) :: tail) [keyCell key, keyCell key]) ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
                issued.support.profile recipe entries (.word previous) second
                (heap before ((.word key, .word previous) :: tail) [keyCell key, keyCell key])) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued next entry second invocation [.word key])

/-- The Source-first two-call law retains actual stage rejection alternatives;
it never assumes either current public call has already completed. -/
theorem twice_from_captured (member : entry ∈ entries)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value))
    (sameHeap : state.heap = heap before ((.word key, .word previous) :: tail))
    (source : entry.source = .closure (function header shape before))
    (entryType : entry.sourceType = .function .word .word)
    (handleType : entry.handle.sourceType = .function .word .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle (.word key) fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous.bitNot) :: tail) [keyCell key]) ∧
    (RestoreAfterFirst (anchor := anchor) (entries := entries) issued before entry key previous tail checkpoint invocation ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [.word key]) := by
  obtain ⟨ordinary, forward⟩ := direct_from_captured issued shape before entry state member key previous tail []
    sameHeap source entryType handleType ready started invocation
  refine ⟨ordinary, ?_⟩
  rcases forward with ⟨_staged, execution, output, complete⟩ | stopped
  · left
    refine ⟨execution, output, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, value, exports, next, nextHeap⟩ :=
      complete executionFuel outputFuel outcome executionBound outputBound resumed
    refine ⟨completion, actual, value, next, nextHeap, ?_⟩
    intro nextFuel second accepted
    have follows := direct_from_captured issued shape before entry next member key previous.bitNot tail [keyCell key]
      nextHeap source entryType handleType exports accepted invocation
    simpa only [Word.bitNot_involutive, List.cons_append, List.nil_append] using follows
  · exact .inr stopped


private theorem map_carrier (entries : List (Word × Word)) :
    publicMap entries = SourceCoreIndexedSession.DataInput.publicValue (.mapping .word .word (dataEntries entries)) := by
  simp only [publicMap, SourceCoreIndexedSession.DataInput.publicValue]
  congr 1
  induction entries with
  | nil => simp only [publicEntries, dataEntries, List.map_nil, SourceCoreIndexedSession.DataInput.publicEntries]
  | cons pair tail ih =>
    simpa only [publicEntries, dataEntries, List.map_cons,
      SourceCoreIndexedSession.DataInput.publicEntries, SourceCoreIndexedSession.DataInput.publicValue] using
        congrArg (List.cons (.word pair.1, .word pair.2)) ih

private theorem map_types (context : SourceSemantics.Context) (entries : List (Word × Word)) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicMap entries) mappingType := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty _ _
  | cons pair tail ih => exact .entry (.word pair.1) (.word pair.2) ih

private theorem map_meaning (entries : List (Word × Word)) :
    RecursiveNamedPublicDataInputs.Means (publicMap entries) (mappingValue (sourceEntries entries)) := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty
  | cons pair tail ih => exact .prepend (.word pair.1) (.word pair.2) ih

section Initial
variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (keyValue previous : Word) (tail : List (Word × Word))
  (call : SelectedCompilationPublicSessionState.StartedCall session key
    [publicMap ((keyValue, previous) :: tail)] options)
  (initial : Initial issued.toIssued call)

/-- A fresh mapping input reaches the returned handle and both subsequent
calls in one session. Each execution budget is obtained before that call runs. -/
def FactoryChain (shape : Shape initial.header.function.source) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (next : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧
          next.heap = heap ⟨[]⟩ (sourceEntries ((keyValue, previous) :: tail)) ∧
          entry.source = .closure (function initial.header shape ⟨[]⟩) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle (.word keyValue) fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              next.heap entry.source [.word keyValue] (.word previous.bitNot)
              (heap ⟨[]⟩ ((.word keyValue, .word previous.bitNot) :: sourceEntries tail) [keyCell keyValue]) ∧
            (RestoreAfterFirst (anchor := initial.header) (entries := [entry]) issued ⟨[]⟩ entry keyValue previous (sourceEntries tail) checkpoint invocation ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued next entry checkpoint invocation [.word keyValue])

/-- The original factory call is independent of Core. Initial mapping metadata
comes from actual startup, not a scalar helper or a completed public call. -/
theorem initial_factory_chain (shape : Shape initial.header.function.source)
    (resultType : initial.header.function.resultType = .function .word .word)
    (invocation : Staging.Recursive.Scope) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue initial.header initial.header invocation ⟨[]⟩
      [mappingValue (sourceEntries ((keyValue, previous) :: tail))]
      (.closure (function initial.header shape ⟨[]⟩))
      (heap ⟨[]⟩ (sourceEntries ((keyValue, previous) :: tail))) ∧
    (FactoryChain issued keyValue previous tail call initial shape invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation
        [mappingValue (sourceEntries ((keyValue, previous) :: tail))]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt initial.header invocation ⟨[]⟩
    (sourceEntries ((keyValue, previous) :: tail))
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [publicMap ((keyValue, previous) :: tail)] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons (map_types _ _) .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings
      [publicMap ((keyValue, previous) :: tail)] [mappingValue (sourceEntries ((keyValue, previous) :: tail))] :=
    .cons (map_meaning _) .nil
  have forward := initial.forward_data_function_plain types meanings (by rw [resultType]; rfl) plain
  refine ⟨plain, ?_⟩
  rcases forward with ⟨_staged, execution, output, complete⟩ | stopped
  · left
    refine ⟨execution, output, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, ready, entry, entryType, source, returned, handleType, next, sameHeap⟩ :=
      complete executionFuel outputFuel outcome executionBound outputBound resumed
    rw [resultType] at entryType handleType
    refine ⟨completion, actual, entry, next, returned, sameHeap, source, ?_⟩
    intro fuel checkpoint accepted
    exact twice_from_captured issued shape ⟨[]⟩ entry next (List.mem_singleton_self _) keyValue previous
      (sourceEntries tail) sameHeap source entryType handleType ready accepted invocation
  · exact .inr stopped
end Initial

/-- Concrete checked compilation and authentic first startup provide every
semantic premise for the factory and its two retained calls. -/
structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture observed.row.original.key [publicMap ((key, previous) :: tail)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  sourceEq : initial.header.function.source = observed.row.original.function.typedBody
  plain : ∀ invocation, RecursiveNamedPublicPhysicalSessionState.PlainValue
    initial.header initial.header invocation ⟨[]⟩ [mappingValue (sourceEntries ((key, previous) :: tail))]
    (.closure (function initial.header shape ⟨[]⟩)) (heap ⟨[]⟩ (sourceEntries ((key, previous) :: tail)))
  forward : ∀ invocation,
    FactoryChain issued key previous tail started.call initial shape invocation ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [mappingValue (sourceEntries ((key, previous) :: tail))]

theorem from_checked_initial (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture observed.row.original.key [publicMap ((key, previous) :: tail)]) :
    Nonempty (InitialMeaning fixture observed key previous tail started) := by
  obtain ⟨row, rowSame, _signatureSame⟩ := observed.row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.resultType))
  have shape : Shape initial.header.function.source := by rw [sourceEq]; exact observed.shape
  have chain := fun invocation => initial_factory_chain issued key previous tail started.call initial shape resultEq invocation
  exact ⟨⟨issued, initial, shape, sourceEq, fun invocation => (chain invocation).1,
    fun invocation => (chain invocation).2⟩⟩

end Tests.SourceCoreSelectedProjectedBitNot.Captured
