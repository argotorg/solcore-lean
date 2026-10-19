import Solcore.Test.SourceCoreGeneralizedExportHandleSteps

/-! The unchanged complete program is run once. Every target resume follows an
independent Source plan; every next plan consumes the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport.SourcePublicRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

def Certified (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) : Prop :=
  ∃ context : Context observed, Nonempty (FullHistory context session wordHandle boolHandle captureHandle seed)

def WordPlanned (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.wordEntry (.word value) (.word value) call)

theorem plan_word (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) :
    WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.wordEntry
    (.data ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩ ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩) call⟩

theorem word_retained {value : Word}
    {call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel}
    (planned : WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def BoolPlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.boolEntry (.bool value) (.bool value) call)

theorem plan_bool (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) :
    BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.boolEntry
    (.data ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩ ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩) call⟩

theorem bool_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel}
    (planned : BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def CapturePlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (CapturedPlan history value call)

theorem plan_capture (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) :
    CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_captured value call⟩

theorem capture_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel}
    (planned : CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions) := do
  match accepted : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) :
    IO (CellAwarePublicHandleStart.StartedCall session handle argument runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle argument runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified generalized export call did not succeed")

private structure PairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  wordHandle : SourceCorePublicValues.Handle
  boolHandle : SourceCorePublicValues.Handle
  same : returned.value = .product (.function wordHandle) (.function boolHandle)

private def pairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (PairOutput returned) := do
  match same : returned.value with
  | .product (.function first) (.function second) => return ⟨first,second,same⟩
  | _ => throw (IO.userError "Source-certified generalized pair output changed")

private structure FunctionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .function handle

private def functionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (FunctionOutput returned) := do
  match same : returned.value with
  | .function handle => return ⟨handle,same⟩
  | _ => throw (IO.userError "Source-certified captured output changed")

/-- All original rows remain compiled and profiled. Each `resume` consumes a
plan built from independent Source semantics at the actual preceding heap. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.make.original.key [.bool true]
  have firstPlan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.make),
      Nonempty (InitialForward selected observed.makeShape true firstStart observed.callableProfile) := by
    obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.typing.wellFormed
    obtain ⟨selected⟩ := whole.select observed.make
    exact ⟨whole,selected,initial_from_source selected observed.makeShape true observed.typing firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let pair ← pairOutput firstResult.val
  have pairHistory : ∃ context : Context observed,
      Nonempty (PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle) := by
    obtain ⟨whole,selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨whole,selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property pair.same⟩
  let seed := Word.ofNatModulo 29
  let captureCall ← namedCall firstResult.val.session observed.capture.original.key [.word seed]
  have capturePlan : ∃ (context : Context observed)
      (history : PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle),
      Nonempty (CapturePlan history seed captureCall) := by
    obtain ⟨context,⟨history⟩⟩ := pairHistory
    exact ⟨context,history,history.plan_capture seed captureCall⟩
  let captureResult ← resume captureCall.checkpoint
  let captured ← functionOutput captureResult.val
  have capturedHistory : Certified observed captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := capturePlan
    exact ⟨context,plan.collected captureResult.property captured.same⟩
  let tickCall ← namedCall captureResult.val.session observed.tick.original.key [.bool false]
  have tickPlan : ∃ (context : Context observed)
      (history : FullHistory context captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed),
      Nonempty (TickPlan history false tickCall) := by
    obtain ⟨context,⟨history⟩⟩ := capturedHistory
    exact ⟨context,history,history.plan_tick false tickCall⟩
  let tickResult ← resume tickCall.checkpoint
  have tickHistory : Certified observed tickResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := tickPlan
    exact ⟨context,plan.retained tickResult.property⟩
  require (tickResult.val.value == .bool false) "Source-certified intervening result changed"
  let wordCall ← handleCall tickResult.val.session pair.wordHandle (.word (Word.ofNatModulo 47))
  have wordPlan := plan_word observed tickHistory (Word.ofNatModulo 47) wordCall
  let wordResult ← resume wordCall.checkpoint
  have wordHistory := word_retained observed wordPlan wordResult.property
  require (wordResult.val.value == .word (Word.ofNatModulo 47)) "Source-certified Word handle result changed"
  let boolCall ← handleCall wordResult.val.session pair.boolHandle (.bool true)
  have boolPlan := plan_bool observed wordHistory true boolCall
  let boolResult ← resume boolCall.checkpoint
  have boolHistory := bool_retained observed boolPlan boolResult.property
  require (boolResult.val.value == .bool true) "Source-certified Bool handle result changed"
  let savedCall ← handleCall boolResult.val.session captured.handle (.bool false)
  have savedPlan := plan_capture observed boolHistory false savedCall
  let savedResult ← resume savedCall.checkpoint
  have savedHistory := capture_retained observed savedPlan savedResult.property
  require (savedResult.val.value == .word seed) "Source-certified captured value changed"
  let repeatCall ← handleCall savedResult.val.session pair.wordHandle (.word (Word.ofNatModulo 61))
  have repeatPlan := plan_word observed savedHistory (Word.ofNatModulo 61) repeatCall
  let repeatResult ← resume repeatCall.checkpoint
  have _finalHistory := word_retained observed repeatPlan repeatResult.property
  require (repeatResult.val.value == .word (Word.ofNatModulo 61)) "Source-certified repeated handle changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,captureResult.val.session.heapSize,
    tickResult.val.session.heapSize,wordResult.val.session.heapSize,boolResult.val.session.heapSize,
    savedResult.val.session.heapSize,repeatResult.val.session.heapSize]
  require (heaps == [4,10,16,19,22,25,28,31]) "Source-certified exported handle heaps changed"
  IO.println "GENERALIZED_EXPORTED_SOURCE_PUBLIC: originals3/cache3/typed3/profile3; make/capture/tick/Word/Bool/captured/reuse"
  IO.println s!"GENERALIZED_EXPORTED_SOURCE_HEAPS: {heaps}"
  IO.println "GENERALIZED_EXPORTED_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreGeneralizedExport.SourcePublicRuntime
