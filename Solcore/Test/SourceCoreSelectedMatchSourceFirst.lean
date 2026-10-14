import Solcore.Test.SourceCoreSelectedMatchFixture

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

/-- Only actual compilation, profile, bootstrap and start receipts precede this
ordinary Source proof. No completed public result is an input. -/
structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = fixture.named.specialized.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word previous, .word seed]
    (.word seed) (sourceHeap seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word previous, .word seed]
      (.value (.word seed)) (sourceHeap seed) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint (.word seed) (sourceHeap seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word previous, .word seed]

theorem from_source (fixture : Fixture) (started : Started fixture) :
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
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified
    (SelectedCompilationCheckedBodyTyping.of_checked fixture.checked fixture.profile) initial.header
  have plain := fun invocation => ordinary_call initial.header fixture.shape sourceEq certified sourceAt invocation previous seed
  have simple : ∀ value ∈ ([.word previous, .word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact .word previous
    · cases List.mem_singleton.mp member; exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word previous, .word seed] initial.header.types := by
    rw [input_types initial.header fixture.shape sourceEq]
    exact .cons ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word previous, .word seed] [.word previous, .word seed] :=
    .cons ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedMatch
