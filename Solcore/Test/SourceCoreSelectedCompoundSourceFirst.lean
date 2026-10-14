import Solcore.Test.SourceCoreSelectedCompoundFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

private theorem word_types (context : SourceSemantics.Context) (left right : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context
      [.word left, .word right] [.word, .word] :=
  .cons ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ (.cons ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ .nil)

private theorem word_meanings (left right : Word) :
    RecursiveNamedPublicDataInputs.Meanings [.word left, .word right] [.word left, .word right] :=
  .cons ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ (.cons ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ .nil)

private theorem word_inputs (entries : List RecursiveNamedPublicFunctionHistory.Entry)
    (context : SourceSemantics.Context) (left right : Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context
      [.word, .word] [.word left, .word right] [.word left, .word right] :=
  .cons (.data ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩)
    (.cons (.data ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩) .nil)

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.addRow.original.key [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.addRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.word (Word.ofNatModulo 42))
    (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.value (.word (Word.ofNatModulo 42)))
        (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word (Word.ofNatModulo 42))
        started.call (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]

/-- Source execution is derived from the observed original body before the
initial public checkpoint completes. The compiler profile remains explicit. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.addRow.original.key [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, signatureSame⟩ := observed.addRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.addRow.resultType))
  have nativeEq : initial.header.output = .word := initial.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans observed.addRow.nativeResult))
  have shape : CompoundShape initial.header.function.source .add := by rw [sourceEq]; exact observed.addShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.word (Word.ofNatModulo 42))
      (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42)) := by
    intro invocation
    exact compound_call initial.header shape sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 37) (Word.ofNatModulo 5)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)],
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] initial.header.types := by
    rw [compound_input_types initial.header shape]
    exact word_types _ _ _
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple types
      (word_meanings _ _) (.word (Word.ofNatModulo 42)) resultEq nativeEq (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure LaterMeaning (row : Row fixture) (operation : Operation) (left right : Word)
    (call : StartedCall session row.original.key [.word left, .word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word left, .word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap [.word left, .word right]
    (.word (operation.apply left right)) (resultHeap state.heap right (operation.apply left right))
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word left, .word right]
        (.value (.word (operation.apply left right))) (resultHeap state.heap right (operation.apply left right)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.word (operation.apply left right))
        call (resultHeap state.heap right (operation.apply left right))) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word left, .word right]

/-- Subsequent arithmetic uses the same issued catalog and exact returned
Source heap; the ordinary trace is independent of public completion. -/
theorem later_from_source (row : Row fixture) {operation : Operation}
    (shape : CompoundShape row.original.function.typedBody operation) (left right : Word)
    (call : StartedCall session row.original.key [.word left, .word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (LaterMeaning issued state row operation left right call) := by
  obtain ⟨eligible, rowSame, signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := request.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans row.resultType))
  have nativeEq : request.header.output = .word := request.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans row.nativeResult))
  have actualShape : CompoundShape request.header.function.source operation := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => compound_call request.header actualShape sourceAt anchor invocation state.heap left right
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word left, .word right] [.word left, .word right] := by
    rw [body_types, compound_input_types request.header actualShape]
    exact word_inputs _ _ _ _
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.scalar issued state call request inputs ready
      (.word (operation.apply left right)) resultEq nativeEq (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture) (right : Word)
    (call : StartedCall session row.original.key [.word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap [.word right]
    (.invalidAssignmentOperands .divide) (missingHeap state.heap right)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word right]
        (.fault (.semantic (.invalidAssignmentOperands .divide))) (missingHeap state.heap right) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.semantic (.invalidAssignmentOperands .divide))
        call (missingHeap state.heap right)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word right]

/-- The absent target faults after evaluating the RHS. This is the same
original body and current heap used by the public failure continuation. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
    (right : Word) (call : StartedCall session row.original.key [.word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row right call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : MissingShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping request.header
  have plain := fun invocation => missing_call request.header actualShape certified sourceAt anchor invocation state.heap right
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word right] [.word right] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .cons (.data ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩) .nil
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.invalidAssignmentOperands .divide) (plain invocation)⟩⟩

/-- Every sufficiently fueled genuine operand failure returns a state for
this same issued catalog, and an independent addition trace starts from that
exact reached heap. No completed call is an input to this continuation. -/
theorem missing_then_reuse (missingRow addRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (addShape : CompoundShape addRow.original.function.typedBody .add)
    (right : Word) (call : StartedCall session missingRow.original.key [.word right] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap right ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.invalidAssignmentOperands .divide)) token ∧
            ∀ nextCall : StartedCall returned addRow.original.key
                [.word (Word.ofNatModulo 20), .word (Word.ofNatModulo 22)] runOptions,
              Nonempty (LaterMeaning issued next addRow .add (Word.ofNatModulo 20)
                (Word.ofNatModulo 22) nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow right call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [.word right] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape right call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact later_from_source issued next addRow addShape (Word.ofNatModulo 20)
      (Word.ofNatModulo 22) nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

end Tests.SourceCoreSelectedCompound
