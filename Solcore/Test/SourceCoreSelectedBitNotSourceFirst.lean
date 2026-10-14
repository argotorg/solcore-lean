import Solcore.Test.SourceCoreSelectedBitNotFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

private theorem word_types (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context [.word value] [.word] :=
  .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil

private theorem word_meanings (value : Word) :
    RecursiveNamedPublicDataInputs.Meanings [.word value] [.word value] :=
  .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil

private theorem word_inputs (entries : List RecursiveNamedPublicFunctionHistory.Entry)
    (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word] [.word value] [.word value] :=
  .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.invertRow.original.key [.word (Word.ofNatModulo 7)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.invertRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7).bitNot)
    (resultHeap ⟨[]⟩ (Word.ofNatModulo 7))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 7)] (.value (.word (Word.ofNatModulo 7).bitNot))
        (resultHeap ⟨[]⟩ (Word.ofNatModulo 7)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word (Word.ofNatModulo 7).bitNot)
        started.call (resultHeap ⟨[]⟩ (Word.ofNatModulo 7))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 7)]

/-- Source execution is derived from the observed original body before the
initial public checkpoint completes. The compiler profile remains explicit. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.invertRow.original.key [.word (Word.ofNatModulo 7)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, signatureSame⟩ := observed.invertRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.invertRow.resultType))
  have nativeEq : initial.header.output = .word := initial.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans observed.invertRow.nativeResult))
  have shape : UnaryShape initial.header.function.source := by rw [sourceEq]; exact observed.invertShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
      [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7).bitNot)
      (resultHeap ⟨[]⟩ (Word.ofNatModulo 7)) := by
    intro invocation
    exact unary_call initial.header shape sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 7)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 7)],
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl; exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 7)] initial.header.types := by
    rw [unary_input_types initial.header shape]
    exact word_types _ _
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple types
      (word_meanings _) (.word (Word.ofNatModulo 7).bitNot) resultEq nativeEq (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure LaterMeaning (row : Row fixture) (value : Word)
    (call : StartedCall session row.original.key [.word value] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word value]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap [.word value]
    (.word value.bitNot) (resultHeap state.heap value)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word value]
        (.value (.word value.bitNot)) (resultHeap state.heap value) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.word value.bitNot)
        call (resultHeap state.heap value)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word value]

/-- Subsequent unary execution uses the same issued catalog and exact returned
Source heap; the ordinary trace is independent of public completion. -/
theorem later_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody) (value : Word)
    (call : StartedCall session row.original.key [.word value] runOptions)
    (ready : session.ExportsReady) : Nonempty (LaterMeaning issued state row value call) := by
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
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => unary_call request.header actualShape sourceAt anchor invocation state.heap value
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact word_inputs _ _ _
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.scalar issued state call request inputs ready
      (.word value.bitNot) resultEq nativeEq (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture)
    (call : StartedCall session row.original.key [] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key []
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap []
    (.invalidUnaryOperand .bitNot) (missingHeap state.heap)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap []
        (.fault (.semantic (.invalidUnaryOperand .bitNot))) (missingHeap state.heap) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.semantic (.invalidUnaryOperand .bitNot))
        call (missingHeap state.heap)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation []

/-- The absent target produces the genuine unary fault without evaluating
an expression. The public failure uses the exact original body and heap. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
     (call : StartedCall session row.original.key [] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row call) := by
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
  have plain := fun invocation => missing_call request.header actualShape certified sourceAt anchor invocation state.heap
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .nil
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.invalidUnaryOperand .bitNot) (plain invocation)⟩⟩

/-- Every sufficiently fueled genuine operand failure returns a state for
this same issued catalog, and an independent complement trace starts from that
exact reached heap. No completed call is an input to this continuation. -/
theorem missing_then_reuse (missingRow invertRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (invertShape : UnaryShape invertRow.original.function.typedBody)
    (call : StartedCall session missingRow.original.key [] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.invalidUnaryOperand .bitNot)) token ∧
            ∀ nextCall : StartedCall returned invertRow.original.key
                [.word (Word.ofNatModulo 7)] runOptions,
              Nonempty (LaterMeaning issued next invertRow (Word.ofNatModulo 7) nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact later_from_source issued next invertRow invertShape (Word.ofNatModulo 7) nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

end Tests.SourceCoreSelectedBitNot
