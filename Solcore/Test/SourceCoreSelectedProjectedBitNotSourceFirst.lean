import Solcore.Test.SourceCoreSelectedProjectedBitNotFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

def publicEntries (entries : List (Word × Word)) :
    List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def sourceEntries (entries : List (Word × Word)) : List (Dynamic.Value × Dynamic.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def dataEntries (entries : List (Word × Word)) :
    List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def publicMap (entries : List (Word × Word)) : SourceCorePublicValues.Value :=
  .mapping .word .word (publicEntries entries)

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

private theorem word_types (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (.word value) .word :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
private theorem word_meaning (value : Word) : RecursiveNamedPublicDataInputs.Means (.word value) (.word value) :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.keyRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7))
    (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 7)] (.value (.word (Word.ofNatModulo 7)))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7)) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe []
        initial.header.function.resultType started.call.checkpoint (.word (Word.ofNatModulo 7))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 7)]

/-- A genuine scalar helper initializes the selected named/header compilation
of the unchanged thirteen-declaration program.
Its ordinary Source trace is built before public completion; later calls use
that issued state's mapping-aware input path. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, _signatureSame⟩ := observed.keyRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have shape : CopyShape initial.header.function.source := by rw [sourceEq]; exact observed.keyShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping initial.header
  have plain := fun invocation => copy_call initial.header shape certified sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 7)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 7)], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl; exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 7)] initial.header.types := by
    rw [copy_input_types initial.header shape]
    exact .cons (word_types _ _) .nil
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple types
      (.cons (word_meaning _) .nil) (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure UnaryMeaning (row : Row fixture) (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
    (mappingValue (sourceEntries ((key, previous.bitNot) :: tail)))
    (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.value (mappingValue (sourceEntries ((key, previous.bitNot) :: tail))))
        (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (mappingValue (sourceEntries ((key, previous.bitNot) :: tail)))
        (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]

/-- Exact original unary syntax determines the whole ordered mapping output. The theorem requires no execution callback. -/
theorem unary_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (UnaryMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => unary_call request.header actualShape sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

structure DefaultMeaning (row : Row fixture) (key : Word)
    (call : StartedCall session row.original.key [publicMap [], .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap [], .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [mappingValue (sourceEntries []), .word key]
    (mappingValue (sourceEntries [(key, (Word.zero).bitNot)]))
    (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries []), .word key]
        (.value (mappingValue (sourceEntries [(key, (Word.zero).bitNot)])))
        (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (mappingValue (sourceEntries [(key, (Word.zero).bitNot)]))
        (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries []), .word key]

/-- The original unary update inserts the complement of the genuine Word default into an empty mapping. -/
theorem default_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody)
    (key : Word)
    (call : StartedCall session row.original.key [publicMap [], .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (DefaultMeaning issued state row key call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => default_call request.header actualShape sourceAt anchor invocation state.heap
    key
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap [], .word key]
      [mappingValue (sourceEntries []), .word key] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture) (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
    (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
    (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.fault (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))))
        (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe
        (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key)))
        call (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]

/-- The original projected unary update reads an uninitialized key local.
The fault precedes snapshot selection and retains its exact allocations. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row key previous tail call) := by
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
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
      (plain invocation)⟩⟩

/-- A genuine failure returns a state for the same selected issued catalog.
The next original complement starts at that exact reached heap. -/
theorem missing_then_reuse (missingRow invertRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (invertShape : UnaryShape invertRow.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session missingRow.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))) token ∧
            ∀ nextCall : StartedCall returned invertRow.original.key
                [publicMap ((key, previous) :: tail), .word key] runOptions,
              Nonempty (UnaryMeaning issued next invertRow key previous tail nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow key previous tail call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape key previous tail call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact unary_from_source issued next invertRow invertShape key previous tail
      nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

/-- The same public catalog executes the authentic for initializer and then
skips its post after the original false condition. -/
theorem initializer_from_source (row : Row fixture)
    (shape : InitializerShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (UnaryMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : InitializerShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => initializer_call request.header actualShape sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, initializer_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

def publicNested (first second previous : Word) : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(.word first, publicMap [(second, previous)])]

private theorem nested_types (context : SourceSemantics.Context) (first second previous : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicNested first second previous) nestedType := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.entry (.word first) (.mapping (.entry (.word second) (.word previous) (.empty _ _))) (.empty _ _))

private theorem nested_meaning (first second previous : Word) :
    RecursiveNamedPublicDataInputs.Means (publicNested first second previous) (nestedValue first second previous) := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.prepend (.word first) (.mapping (.prepend (.word second) (.word previous) .empty)) .empty)

structure NestedMeaning (row : Row fixture) (first second previous : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key
    [publicNested first second previous, .word first, .word second]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [nestedValue first second previous, .word first, .word second]
    (.word previous.bitNot) (nestedHeap state.heap first second previous.bitNot)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [nestedValue first second previous, .word first, .word second]
        (.value (.word previous.bitNot)) (nestedHeap state.heap first second previous.bitNot) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (.word previous.bitNot)
        (nestedHeap state.heap first second previous.bitNot)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [nestedValue first second previous, .word first, .word second]

/-- The original two-key source trace connects to the same whole public
issuer; both key evaluations and the exact three parameter cells are retained. -/
theorem nested_from_source (row : Row fixture) (shape : NestedShape row.original.function.typedBody)
    (first second previous : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second] runOptions)
    (ready : session.ExportsReady) : Nonempty (NestedMeaning issued state row first second previous call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : NestedShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => nested_call request.header actualShape sourceAt anchor invocation state.heap first second previous
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicNested first second previous, .word first, .word second]
      [nestedValue first second previous, .word first, .word second] := by
    rw [body_types, nested_input_types request.header actualShape]
    exact .cons (.data (nested_types _ _ _ _) (nested_meaning _ _ _))
      (.cons (.data (word_types _ _) (word_meaning _))
        (.cons (.data (word_types _ _) (word_meaning _)) .nil))
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

/-- The independent bootstrap trace supplies the actual state for the first
mapping complement in the same issued session. No completed call is assumed. -/
theorem initial_then_invert (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)])
    (key previous : Word) (tail : List (Word × Word)) :
    ∃ meaning : InitialMeaning fixture observed started, ∀ invocation,
      (∃ requiredExecution requiredOutput,
        ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome started.artifact),
          requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
          started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
          ∃ completion : SourceCoreExecution.Completion started.artifact,
            outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
            ∃ next : meaning.issued.toIssued.State meaning.initial.header completion.session [],
              next.heap = copyHeap ⟨[]⟩ (Word.ofNatModulo 7) ∧
              ∀ nextCall : StartedCall completion.session observed.invertRow.original.key
                  [publicMap ((key, previous) :: tail), .word key] runOptions,
                Nonempty (UnaryMeaning meaning.issued next observed.invertRow key previous tail nextCall)) ∨
      SelectedCompilationStageClosedInitialForward.StageStopped meaning.issued started.call
        meaning.initial invocation [.word (Word.ofNatModulo 7)] := by
  obtain ⟨meaning⟩ := initial_from_source fixture observed profile started
  refine ⟨meaning, ?_⟩
  intro invocation
  rcases meaning.forward invocation with finished | stopped
  · obtain ⟨requiredExecution, requiredOutput, forward⟩ := finished.2
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨completion, outcomeEq, ready, next, heapEq, _value, _handles⟩ :=
      forward executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    refine ⟨completion, outcomeEq, ready, next, heapEq, ?_⟩
    intro nextCall
    exact unary_from_source meaning.issued next observed.invertRow observed.invertShape key previous
      tail nextCall ready
  · exact .inr stopped

end Tests.SourceCoreSelectedProjectedBitNot
