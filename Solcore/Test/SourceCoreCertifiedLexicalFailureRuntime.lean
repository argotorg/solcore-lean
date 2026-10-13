import Solcore.Test.SourceCoreCertifiedLexicalFailureHeaders
import Solcore.Test.SourceCoreInitialLexicalFailureRuntime
import Solcore.Test.SourceCoreDirectFailureRuntime

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

abbrev First (fixture : CompiledFixture) (observed : ObservedProgram fixture) :=
  Tests.SourceCoreDirectFailure.ObservedPublicRun fixture observed

def first_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : RecursiveNamedPublicPhysicalSessionState.StartedCall
      first.session observed.failedRow.row.key [] runOptions := ⟨first.checkpoint, first.started⟩

def original_first {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : ObservedPublicRun fixture observed := {
  artifact := first.artifact, opened := first.opened, bootstrap := first.bootstrap,
  fresh := first.fresh, session := first.session, ready := first.ready,
  checkpoint := first.checkpoint, started := first.started, reason := first.reason,
  returned := first.returned, executed := first.executed }

def continuation_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {first : First fixture observed} (next : ObservedContinuation (original_first first)) :
    RecursiveNamedPublicPhysicalSessionState.Call first.returned observed.identityRow.row.key [.word seed] runOptions :=
  ⟨⟨next.checkpoint, next.started⟩, next.completion, next.executed⟩

theorem first_returned_ready {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : first.returned.ExportsReady := by
  obtain ⟨_artifact, _session, checkpoint, _root, _world, _store, _native, _values,
      _opened, _prepared, atSession, atCheckpoint, started⟩ := first.start_receipt
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := first.executed
  have same : publicCheckpoint = first.checkpoint := Except.ok.inj (accepted.symm.trans first.started)
  subst publicCheckpoint
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (started.original.initial_registry.exportsReady (atSession.exportsReady_iff.mp ready)))

structure FreshIdentity (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.Call session observed.identityRow.row.key [.word seed] runOptions
  returned : call.completion.value = .word seed

def observeFreshIdentity (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (FreshIdentity fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "original identity bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.identityRow.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "original fresh identity failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "original fresh identity exhausted")
      | .ok (.succeeded completion) =>
        if returned : completion.value = .word seed then
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            ⟨⟨checkpoint, started⟩, completion, result ▸ executed.property⟩, returned⟩
        else throw (IO.userError "original fresh identity did not return37")

end Tests.SourceCoreCertifiedLexicalFailure
