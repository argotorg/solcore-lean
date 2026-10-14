import Solcore.Test.SourceCoreSelectedLexicalSourceStart
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward

/-! Independent ordinary traces drive the closed public compiler theorem for
the original lexical program. Initialization is observed before execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalSourceFirst
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedLexicalOrdinaryTraces
open Tests.SourceCoreSelectedLexicalSourceStart
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure ScalarConclusion (issued : Profiled fixture.recipe)
    (started : Started fixture observed.identityRow.row.key [.word seed]) where
  initial : Initial issued.toIssued started.call
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : actual.header = initial.header
  invocation : Staging.Recursive.Scope
  plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed] (.word seed)
    (appendWord ⟨[]⟩ (some (.word seed)))
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed] (.value (.word seed))
      (appendWord ⟨[]⟩ (some (.word seed))) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word seed) started.call
        (appendWord ⟨[]⟩ (some (.word seed)))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

structure FaultConclusion (issued : Profiled fixture.recipe)
    (started : Started fixture observed.failedRow.row.key []) where
  initial : Initial issued.toIssued started.call
  actual : ActualHeader fixture observed.failedRow.row
  headerEq : actual.header = initial.header
  invocation : Staging.Recursive.Scope
  plain : PlainFault initial.header initial.header invocation ⟨[]⟩ []
    (.uninitializedLocation (nextLocation ⟨[]⟩)) (appendWord ⟨[]⟩ none)
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ []
      (.fault (.semantic (.uninitializedLocation (nextLocation ⟨[]⟩)))) (appendWord ⟨[]⟩ none) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe
        (.semantic (.uninitializedLocation (nextLocation ⟨[]⟩))) started.call (appendWord ⟨[]⟩ none)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation []

theorem scalar_from_source
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow)
    (started : Started fixture observed.identityRow.row.key [.word seed]) :
    ∃ issued : Profiled fixture.recipe, Nonempty (ScalarConclusion issued started) := by
  obtain ⟨issued, initial, actual, actualEq⟩ := initial profile observed.identityRow started
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] initial.header.function
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed] (.word seed)
      (appendWord ⟨[]⟩ (some (.word seed))) := by
    have trace := Tests.SourceCoreSelectedLexicalOrdinaryTraces.ActualHeader.identity_plain actual (actualEq.symm ▸ sourceAt) initial.header invocation ⟨[]⟩ seed
    simpa only [actualEq] using trace
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, identity_types actual]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] := .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have raw : initial.header.function.resultType = .word := by rw [← actualEq]; exact identity_result actual
  have native : initial.header.output = .word := by rw [← actualEq]; exact identity_output actual
  exact ⟨issued, ⟨⟨initial, actual, actualEq, invocation, plain,
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple inputTypes meanings
      (.word seed) raw native plain⟩⟩⟩

theorem fault_from_source
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.failedRow)
    (started : Started fixture observed.failedRow.row.key []) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FaultConclusion issued started) := by
  obtain ⟨issued, initial, actual, actualEq⟩ := initial profile observed.failedRow started
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] initial.header.function
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : PlainFault initial.header initial.header invocation ⟨[]⟩ []
      (.uninitializedLocation (nextLocation ⟨[]⟩)) (appendWord ⟨[]⟩ none) := by
    have trace := Tests.SourceCoreSelectedLexicalOrdinaryTraces.ActualHeader.failed_plain actual (actualEq.symm ▸ sourceAt) initial.header invocation ⟨[]⟩
    simpa only [actualEq] using trace
  have simple : ∀ value ∈ ([] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by intro value member; cases member
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [] initial.header.types := by
    rw [← actualEq, failed_types actual]
    exact .nil
  exact ⟨issued, ⟨⟨initial, actual, actualEq, invocation, plain,
    SelectedCompilationStageClosedInitialForward.fault issued started.call initial simple inputTypes .nil
      (.uninitializedLocation (nextLocation ⟨[]⟩)) plain⟩⟩⟩

end Tests.SourceCoreSelectedLexicalSourceFirst
