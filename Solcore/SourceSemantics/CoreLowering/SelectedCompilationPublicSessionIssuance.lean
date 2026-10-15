import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues

/-! Genuine public issuance appends the exact named or builtin handle to the
positive physical history. The Source heap, physical cache and earlier entries
remain the same because issuance preserves the actual native runtime. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState

private theorem indexed_artifact_eq
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {leftArtifact rightArtifact : SourceCoreIndexedSession.Artifact}
    {left : SourceCoreIndexedSession.Session leftArtifact} {right : SourceCoreIndexedSession.Session rightArtifact}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : leftArtifact = rightArtifact := by
  rcases artifact with ⟨compilation, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected native atRecipe =>
      cases session
      exact first.1.symm.trans second.1

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- The genuine named factory's complete captured environment is retained as
one positive history entry, with its exact Source and public handle types. -/
theorem State.remember_named
    (support : SelectedCompilationPhysicalProgramSupport.Support
      compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    {issued : SourceCoreExecution.Completion artifact} {fuel : Nat}
    (issuance : session.NamedIssuedAt packet.header.named.signature.key fuel issued)
    {handle : SourceCorePublicValues.Handle} (handleValue : issued.value = .function handle) :
    ∃ entry : Entry,
      entry.sourceType = packet.header.named.specialized.function.type ∧
      entry.source = .global (CallableNamedReversal.global
        (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)) ∧
      entry.handle = handle ∧ handle.sourceType = packet.header.named.specialized.function.type ∧
      ∃ next : State rows anchor initial profile recipe issued.session (entries ++ [entry]),
        next.heap = state.heap := by
  have certified := SelectedCompilationNamedArgumentRows.certified_at packet.sourceAt support.bodyTyping
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq state.atSession beforeAt
  cases sameArtifact
  have sameSession := state.atSession.unique beforeAt
  cases sameSession
  have actualHandle := completedAt.1.symm.trans handleValue
  obtain ⟨native, encoded, _represented, _typed⟩ :=
    SelectedCompilationPublicFactoryValues.Session.named_value_represents_current
      prepared inputs rows packet member initial.result.context.registry state.receiving.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      profile state.caller anchor actualIssuance state.history.semantic.current.1 (.refl _)
      state.atRecipe actualHandle certified
  have sourceType := SelectedCompilationPublicFactoryValues.Session.named_source_type
    prepared packet actualIssuance state.atRecipe
  have handleType := (actualIssuance.function_source_type actualHandle).trans sourceType
  let entry : Entry := ⟨packet.header.named.specialized.function.type,
    .global (CallableNamedReversal.global
      (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
    handle, native, CallableContract.functionType packet.header.named.signature.parameterType
      packet.header.named.signature.resultType, fuel⟩
  have history := RecursiveNamedPublicFunctionHistory.History.remember_issued state.history.semantic
    (.preparedPhysicalNamedSelected prepared inputs rows packet member initial.result.context.registry
      state.receiving.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      profile anchor actualIssuance state.atRecipe actualHandle encoded certified)
  let next : State rows anchor initial profile recipe issued.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := state.mapping
    world := state.world
    heap := state.heap
    store := state.store
    caller := state.caller
    atSession := completedAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := actualIssuance.same_runtime.registry_at state.registry
    history := ⟨history, state.history.physical⟩ }
  exact ⟨entry, rfl, rfl, rfl, handleType, next, rfl⟩

/-- The builtin entry is derived from the compiler's actual closed factory;
all earlier captured closures keep their exact Source heap and physical slots. -/
theorem State.remember_builtin
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    (function : BuiltinFunctionId)
    {issued : SourceCoreExecution.Completion artifact} {fuel : Nat}
    (issuance : session.BuiltinIssuedAt function fuel issued)
    {handle : SourceCorePublicValues.Handle} (handleValue : issued.value = .function handle) :
    ∃ entry : Entry,
      entry.sourceType = function.type ∧ entry.source = .builtin ⟨function⟩ ∧
      entry.handle = handle ∧ handle.sourceType = function.type ∧
      ∃ next : State rows anchor initial profile recipe issued.session (entries ++ [entry]),
        next.heap = state.heap := by
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq state.atSession beforeAt
  cases sameArtifact
  have sameSession := state.atSession.unique beforeAt
  cases sameSession
  have actualHandle := completedAt.1.symm.trans handleValue
  obtain ⟨native, _sameRuntime, sourceType, encoded, _represented, _typed⟩ :=
    SelectedCompilationPublicFactoryValues.Session.builtin_value_represents_after
      prepared (headers rows) (keys compiled) initial.result.context.registry state.receiving.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      profile state.mapping anchor.function.context state.heap actualIssuance (.refl _)
      state.atRecipe actualHandle (world := state.world)
  have handleType := (actualIssuance.function_source_type actualHandle).trans sourceType
  let entry : Entry := ⟨function.type, .builtin ⟨function⟩, handle, native,
    CallableContract.functionType (SourceCoreInteger.builtinParameter function)
      (SourceCoreInteger.builtinResult function), fuel⟩
  have history := RecursiveNamedPublicFunctionHistory.History.remember_issued state.history.semantic
    (.preparedPhysicalBuiltin prepared (headers rows) (keys compiled) initial.result.context.registry
      state.receiving.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      profile anchor actualIssuance state.atRecipe actualHandle encoded)
  let next : State rows anchor initial profile recipe issued.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := state.mapping
    world := state.world
    heap := state.heap
    store := state.store
    caller := state.caller
    atSession := completedAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := actualIssuance.same_runtime.registry_at state.registry
    history := ⟨history, state.history.physical⟩ }
  exact ⟨entry, rfl, rfl, rfl, handleType, next, rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
