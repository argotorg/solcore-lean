import Solcore.Test.SourceCoreSelectedCoercedDirectSourceFirst

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 300000, outputValidationFuel := 2048}

structure Started (fixture : Fixture) (flag : Bool) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.make.named.signature.key [.bool flag] runOptions

def observeStarted (fixture : Fixture) (flag : Bool) : IO (Started fixture flag) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "coerced bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.make.named.signature.key [.bool flag] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

/-- Automatic issuance supplies the real factory and generic callee headers.
Both ordinary traces are constructed before either target call is resumed. -/
theorem from_source (fixture : Fixture) (flag : Bool) (started : Started fixture flag) :
    ∃ (issued : Profiled fixture.recipe) (initial : Initial issued.toIssued started.call)
      (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header),
      ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.bool flag]
        (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag) ∧
        (ForwardChain fixture issued flag started.call initial makeFacts invocation ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.bool flag]) ∧
        ((SourceCall initial.header initial.header invocation ⟨[]⟩ [.bool flag]
            (.value (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts)))) (capturedHeap flag) ∧
          SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
            issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint
            (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag)) ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.bool flag]) := by
  let row : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled
      fixture.make.named.signature.key :=
    ⟨fixture.make.named, fixture.make.index, fixture.make.named.signature, fixture.make.cached,
      CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot _ fixture.make.cached, rfl, fixture.make.eligible⟩
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  obtain ⟨input, packet, _retained, sameHeader⟩ := issued.catalog.rows.mem_headers initial.header initial.start.selected.member
  have sameRow : input.row = fixture.make.named.specialized :=
    input.prepared.same.symm.trans (congrArg (·.specialized)
      (packet.aligned.named.symm.trans ((congrArg (·.named) sameHeader).trans namedEq)))
  have makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header :=
    sameHeader ▸ header_facts packet sameRow fixture.resolved
  obtain ⟨keepInput, keepPacket, _keepRetained, keepRow, _slot, _same⟩ :=
    issued.catalog.packet_at fixture.keep.cached fixture.keep.eligible
  have keepFacts := header_facts keepPacket keepRow fixture.keepResolved
  have resultType := makeFacts.result.trans fixture.makeResult
  refine ⟨issued, initial, makeFacts, ?_⟩
  intro invocation
  have first := initial_source_first fixture issued flag started.call initial (keepFacts := keepFacts) makeFacts resultType invocation
  exact ⟨first.1, first.2, initial_whole_output fixture issued flag started.call initial makeFacts invocation⟩

end Tests.SourceCoreSelectedCoercedDirect
