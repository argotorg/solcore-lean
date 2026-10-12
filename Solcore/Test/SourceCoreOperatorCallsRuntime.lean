import Solcore.Test.SourceCoreOperatorCallsFixture
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry

/-! Actual unary/conditional/arithmetic expressions call an authentically issued
named handle. Both selected branches retain their original execution receipts
and consume the exact preceding returned session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstValue : Core.Word := Core.Word.ofNatModulo 11
def secondValue : Core.Word := Core.Word.ofNatModulo 22
def zero : Core.Word := Core.Word.ofNatModulo 0
def issuanceFuel : Nat := 1000

structure ObservedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observePublicCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) (value : Core.Word) :
    IO (ObservedCall session key arguments value) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "operator call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "operator call exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "operator call returned an unexpected Word")

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok issued =>
    match returned : issued.val.value with
    | .function handle => pure ⟨issued.val, issued.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall session observed.identityRow.row.key [.word seed] seed

def observeInitial (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named operators bootstrap exhausted")
  | .ready session =>
    let call ← observePublicCall session observed.identityRow.row.key [.word seed] seed
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

def selectArguments (handle : SourceCorePublicValues.Handle) (flag : Bool) (value : Core.Word) : List SourceCorePublicValues.Value :=
  [.function handle, .bool flag, .word value]

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  initial : ObservedInitial fixture observed
  named : ObservedNamed initial.call.completion.session observed.identityRow.row.key
  first : ObservedCall named.completion.session observed.selectRow.row.key (selectArguments named.handle false firstValue) secondValue
  next : ObservedCall first.completion.session observed.selectRow.row.key (selectArguments named.handle true secondValue) zero

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let named ← observeNamed initial.call.completion.session observed.identityRow.row.key
  let first ← observePublicCall named.completion.session observed.selectRow.row.key (selectArguments named.handle false firstValue) secondValue
  let next ← observePublicCall first.completion.session observed.selectRow.row.key (selectArguments named.handle true secondValue) zero
  return ⟨initial, named, first, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.identityRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.identityRow.row.key [.word seed]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.identityRow.row.key [.word seed]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  have same := List.mem_singleton.mp member
  exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed

end Tests.SourceCoreOperatorCalls
