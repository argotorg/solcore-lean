import Solcore.Test.SourceCoreSelectedGeneralizedLocalPublic
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation

/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

def InitialForward.Stopped (first : InitialForward selected shape firstFlag firstStart callableProfile) : Prop :=
  ∃ origin call reason reached,
  ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers selected.rows)
    (owner fixture.original.recipe.compiled).key selected.packet.header [] first.start.world,
  ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → first.start.checkpoint.NativeDone fuel value finalStore) ∧
    CellAwarePublicApplicationResult.NamedResultAt
      (registry := first.initial.receiving.result.context.registry)
      first.functions (first.cells first.initial.receiving.result.context.registry)
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val selected.packet.header capture
      first.start.native selected.packet.header.context (.fault (.stage origin call reason)) reached
      value finalStore finalMap finalWorld
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults first.initial.receiving.result.diagnostics)

/-- Successful public output manufactures the continuation state from its exact
returned history. The other branch keeps the actual earlier stage rejection. -/
theorem InitialForward.retained (first : InitialForward selected shape firstFlag firstStart callableProfile) :
    (∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome firstStart.artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        firstStart.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion firstStart.artifact)
          (retained : first.Retained returned.session []),
          outcome = .succeeded returned ∧
          retained.state.heap = (selected.shape shape).finalHeap selected.packet.header.context
            (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ firstFlag) firstFlag) ∨
    first.Stopped := by
  rcases first.forward with success | stopped
  · obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _result, output⟩ := success
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enough outputEnough resumed
    obtain ⟨returned, actual, generation, caller, succeeded, _nativeResult, atReturned, _related,
      history, registry, exportsReady⟩ := output executionFuel outputFuel outcome enough outputEnough resumed
    exact ⟨returned, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := finalMap, world := finalWorld,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ firstFlag) firstFlag,
      store := finalStore, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩, succeeded, rfl⟩
  · exact .inr stopped

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.word (Word.ofNatModulo 11)) (.bool flag))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag retained.state.heap)
      (flagHeap retained.state.heap flag) flag)

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, forward⟩⟩

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

def NextForward.Stopped (next : NextForward first retained flag call) : Prop :=
  ∃ origin stageCall reason reached,
  ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers selected.rows)
    (owner fixture.original.recipe.compiled).key selected.packet.header
    retained.state.mapping retained.state.world,
  ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → next.start.checkpoint.NativeDone fuel value finalStore) ∧
    CellAwarePublicApplicationResult.NamedResultAt
      (registry := next.ready.receiving.result.context.registry)
      first.functions (first.cells next.ready.receiving.result.context.registry)
      (owner fixture.original.recipe.compiled) retained.state.caller selected.packet.header capture
      next.start.payloads selected.packet.header.context (.fault (.stage origin stageCall reason)) reached
      value finalStore finalMap finalWorld
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.ready.receiving.result.diagnostics)

/-- Repeated calls keep the actual returned heap, receiver and full history.
The initial model remains fixed while each call uses its current decoder. -/
theorem NextForward.retains_state (next : NextForward first retained flag call) :
    (∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion artifact)
          (continued : first.Retained returned.session entries),
          outcome = .succeeded returned ∧
          continued.state.heap = (selected.shape shape).finalHeap selected.packet.header.context
            (flagEnvironment (selected.shape shape).flag retained.state.heap)
            (flagHeap retained.state.heap flag) flag) ∨
    next.Stopped := by
  rcases next.forward with success | stopped
  · obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _result, output⟩ := success
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enough outputEnough resumed
    obtain ⟨returned, actual, generation, caller, succeeded, _nativeResult, atReturned, _related,
      history, registry, exportsReady⟩ := output executionFuel outputFuel outcome enough outputEnough resumed
    exact ⟨returned, ⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := finalMap, world := finalWorld,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag retained.state.heap)
        (flagHeap retained.state.heap flag) flag,
      store := finalStore, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩, succeeded, rfl⟩
  · exact .inr stopped

end Tests.SourceCoreSelectedGeneralizedLocal
