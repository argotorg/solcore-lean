import Solcore.Test.SourceCoreMixedBuiltinHandleObserved
import Solcore.Test.SourceCoreMixedBuiltinValueObserved

/-! The complete original fixture and actual returned export retain one genuine
builtin entry through both direct applications and later named calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue.HandlePublic
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure Observed where
  fixture : ProfiledFixture
  row : Row fixture.original
  shape : Shape row.original.function.typedBody
  typing : OriginalTyping fixture.original
  result : row.original.function.inferredBodyType = .product .bool (.function .word .integer)
  callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observe : IO Observed := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "builtinPair"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨result⟩ ← observed (row.original.function.inferredBodyType = .product .bool (.function .word .integer))
    "original builtin output type changed"
  let ⟨profile⟩ ← observed (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "builtin callable profile disabled"
  pure ⟨fixture,row,shape,typing,result,profile⟩

structure Context (observed : Observed) where
  selected : SelectedInventory observed.fixture observed.row
  firstStart : Started observed.fixture.original observed.row.original.key [.bool true]
  first : InitialForward selected observed.shape true firstStart observed.callableProfile

structure History {observed : Observed} (context : Context observed)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) where
  entries : List Entry
  retained : context.first.Retained session entries
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function .word .integer
  sourceEq : entry.source = .builtin ⟨.wordToInteger⟩

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {handle : SourceCorePublicValues.Handle}

theorem Context.collected (context : Context observed)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion context.firstStart.artifact}
    (resumed : context.firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (same : returned.value = .product (.bool true) (.function handle)) :
    Nonempty (History context returned.session handle) := by
  have types := context.selected.result_eq.trans observed.result
  obtain ⟨entries,retained,payload,selected⟩ := context.first.observed_collected observed.typing resumed
    (builtinSelection types same)
  obtain ⟨native,nativeType,fuel,entriesEq⟩ := builtin_selected types same selected
  subst entries
  exact ⟨⟨_,retained,⟨.function .word .integer,.builtin ⟨.wordToInteger⟩,handle,native,nativeType,fuel⟩,by simp,rfl,rfl,rfl⟩⟩

def atEntry {entry : Entry} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (same : entry.handle = handle)
    (call : CellAwarePublicHandleStart.StartedCall session handle argument fuel) :
    CellAwarePublicHandleStart.StartedCall session entry.handle argument fuel :=
  ⟨call.checkpoint,by rw [same]; exact call.accepted⟩

structure HandleStep (history : History context session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) where
  plan : BuiltinHandlePlan context.first history.retained history.entry word (atEntry history.handleEq call)

theorem History.plan_handle (history : History context session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) :
    Nonempty (HandleStep history word call) := by
  obtain ⟨plan⟩ := builtin_plan context.first history.retained history.entry word
    (atEntry history.handleEq call) history.member history.entryType history.sourceEq
  exact ⟨⟨plan⟩⟩

theorem HandleStep.retained {history : History context session handle} {word : Word}
    {call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel}
    (step : HandleStep history word call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (History context returned.session handle) := by
  obtain ⟨retained,_heapEq⟩ := step.plan.observed_retained resumed
  exact ⟨⟨history.entries,retained,history.entry,history.member,history.handleEq,history.entryType,history.sourceEq⟩⟩

structure NamedStep (history : History context session handle) (flag : Bool)
    (call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions) where
  plan : NextForward context.first history.retained flag call

theorem History.plan_named (history : History context session handle) (flag : Bool)
    (call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions) :
    Nonempty (NamedStep history flag call) := by
  obtain ⟨plan⟩ := next_from_source context.first history.retained flag observed.typing call
  exact ⟨⟨plan⟩⟩

theorem NamedStep.retained {history : History context session handle} {flag : Bool}
    {call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions}
    (step : NamedStep history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (History context returned.session handle) := by
  obtain ⟨retained⟩ := step.plan.observed_retained observed.typing resumed
  exact ⟨⟨history.entries,retained,history.entry,history.member,history.handleEq,history.entryType,history.sourceEq⟩⟩

end Tests.SourceCoreMixedBuiltinValue.HandlePublic
