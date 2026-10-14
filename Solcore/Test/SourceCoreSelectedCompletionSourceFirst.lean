import Solcore.Test.SourceCoreSelectedCompletionFixture

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue SourceCall)

def Example.types : Example → List TypeSystem.Ty
  | .branch _ => [.bool, .word]
  | .tail | .letUnit => [.word]
  | .unit => []

theorem Fixture.input_types {spec : Example} (fixture : Fixture spec)
    (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (sourceEq : header.function.source = fixture.named.specialized.function.typedBody) :
    header.types = spec.types := by
  cases spec with
  | branch flag => exact branch_input_types header fixture.shape sourceEq
  | tail =>
    have shape : TailShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact tail_input_types header shape
  | unit =>
    have shape : UnitShape header.function.source := by rw [sourceEq]; exact fixture.shape.down
    exact unit_input_types header shape
  | letUnit =>
    have shape : LetUnitShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact let_unit_input_types header shape

theorem Fixture.ordinary_call {spec : Example} (fixture : Fixture spec)
    (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (sourceEq : header.function.source = fixture.named.specialized.function.typedBody)
    (resultEq : header.function.resultType = spec.resultType)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) :
    PlainValue header header invocation ⟨[]⟩ spec.values spec.result spec.heap := by
  cases spec with
  | branch flag => exact branch_call header fixture.shape sourceEq certified sourceAt invocation flag (Word.ofNatModulo 37)
  | tail =>
    have shape : TailShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact tail_call header shape sourceAt invocation (Word.ofNatModulo 37)
  | unit =>
    have shape : UnitShape header.function.source := by rw [sourceEq]; exact fixture.shape.down
    exact unit_call header shape resultEq sourceAt invocation
  | letUnit =>
    have shape : LetUnitShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact let_unit_call header shape resultEq certified sourceAt invocation (Word.ofNatModulo 37)

/-- Actual checking, compilation and startup are the only preceding receipts.
The ordinary Source execution is constructed before public execution completes. -/
structure InitialMeaning {spec : Example} (fixture : Fixture spec) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = fixture.named.specialized.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ spec.values spec.result spec.heap
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ spec.values (.value spec.result) spec.heap ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint spec.result spec.heap) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation spec.values

theorem from_source {spec : Example} (fixture : Fixture spec) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) (namedEq.trans rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) (namedEq.trans rowSame)).trans fixture.resultType)
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified
    (SelectedCompilationCheckedBodyTyping.of_checked fixture.checked fixture.profile) initial.header
  have plain := fun invocation => fixture.ordinary_call initial.header sourceEq resultEq certified sourceAt invocation
  have simple : ∀ value ∈ spec.arguments, SourceCoreIndexedSession.SimplePublic value := by
    cases spec with
    | branch flag =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact .bool flag
      · cases List.mem_singleton.mp member; exact .word (Word.ofNatModulo 37)
    | tail | letUnit =>
      intro value member
      cases List.mem_singleton.mp member; exact .word (Word.ofNatModulo 37)
    | unit => intro value member; cases member
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context spec.arguments initial.header.types := by
    rw [fixture.input_types initial.header sourceEq]
    cases spec with
    | branch flag =>
      exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        (.cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil)
    | tail | letUnit => exact .cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil
    | unit => exact .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings spec.arguments spec.values := by
    cases spec with
    | branch flag =>
      exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        (.cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil)
    | tail | letUnit => exact .cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil
    | unit => exact .nil
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedCompletion
