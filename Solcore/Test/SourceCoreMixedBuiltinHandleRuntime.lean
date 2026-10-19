import Solcore.Test.SourceCoreMixedBuiltinHandleHistory

/-! Every resume follows an independent Source plan. The original exported
builtin remains usable after a later factory call in the same mixed session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue.HandleRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open HandlePublic

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}

def Certified (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) : Prop :=
  ∃ context : Context observed, Nonempty (History context session handle)

def Planned (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : History context session handle), Nonempty (HandleStep history word call)

theorem plan_handle (certified : Certified observed session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) :
    Planned observed word call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_handle word call⟩

theorem retained {word : Word}
    {call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel}
    (planned : Planned observed word call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session handle := by
  obtain ⟨context,history,⟨step⟩⟩ := planned
  exact ⟨context,step.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (word : Word) :
    IO (CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle (.word word) runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key [.bool flag] runOptions) := do
  match accepted : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified builtin call did not succeed")

private structure Output {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .product (.bool true) (.function handle)

private def output {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (Output returned) := do
  match same : returned.value with
  | .product (.bool true) (.function handle) => return ⟨handle,same⟩
  | _ => throw (IO.userError "original returned builtin output changed")

/-- Complete original1/cache1/profile1, including actual builtin return,
current packed invocation, intervening named call and original handle reuse. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.row.original.key [.bool true]
  have firstPlan : ∃ selected : SelectedInventory observed.fixture observed.row,
      Nonempty (InitialForward selected observed.shape true firstStart observed.callableProfile) := by
    obtain ⟨selected⟩ := observed.fixture.inventory observed.row observed.typing.wellFormed
    exact ⟨selected,initial_from_source selected observed.shape true observed.typing firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let builtin ← output firstResult.val
  have firstHistory : Certified observed firstResult.val.session builtin.handle := by
    obtain ⟨selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property builtin.same⟩
  let firstWord := Word.ofNatModulo 17
  let firstCall ← handleCall firstResult.val.session builtin.handle firstWord
  have firstCallPlan := plan_handle observed firstHistory firstWord firstCall
  let applied ← resume firstCall.checkpoint
  have appliedHistory := retained observed firstCallPlan applied.property
  require (applied.val.value == .integer 17) "Source-certified builtin integer17 changed"
  let nextCall ← namedCall applied.val.session observed.row.original.key false
  have nextPlan : ∃ (context : Context observed) (history : History context applied.val.session builtin.handle),
      Nonempty (NamedStep history false nextCall) := by
    obtain ⟨context,⟨history⟩⟩ := appliedHistory
    exact ⟨context,history,history.plan_named false nextCall⟩
  let nextResult ← resume nextCall.checkpoint
  have nextHistory : Certified observed nextResult.val.session builtin.handle := by
    obtain ⟨context,history,⟨step⟩⟩ := nextPlan
    exact ⟨context,step.retained nextResult.property⟩
  let .product (.bool false) (.function _) := nextResult.val.value
    | throw (IO.userError "intervening original factory output changed")
  let secondWord := Word.ofNatModulo 23
  let reusedCall ← handleCall nextResult.val.session builtin.handle secondWord
  have reusedPlan := plan_handle observed nextHistory secondWord reusedCall
  let reused ← resume reusedCall.checkpoint
  have _finalHistory := retained observed reusedPlan reused.property
  require (reused.val.value == .integer 23) "Source-certified reused builtin integer23 changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,applied.val.session.heapSize,
    nextResult.val.session.heapSize,reused.val.session.heapSize]
  require (heaps == [2,11,11,20,20]) "Source-certified builtin retained heaps changed"
  IO.println "MIXED_BUILTIN_HANDLE_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; factory/Word17/factory/Word23; proof before every resume"
  IO.println s!"MIXED_BUILTIN_HANDLE_SOURCE_HEAPS: {heaps}"
  IO.println "MIXED_BUILTIN_HANDLE_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreMixedBuiltinValue.HandleRuntime
