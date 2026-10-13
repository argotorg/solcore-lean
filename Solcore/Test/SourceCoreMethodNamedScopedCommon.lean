import Solcore.Test.SourceCoreMethodNamedScopedInventory
import Solcore.Test.SourceCoreMethodNamedScopedRuntime
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodNamedScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩


structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.wordRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def OrdinaryInventory.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions (headers inventory.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem OrdinaryInventory.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      (inventory.functions receiver) (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers inventory.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicPhysicalHistory.History (headers := headers inventory.rows)
    (keys := keys fixture.recipe.compiled) (functions := inventory.functions receiver)
    (receiving := receiving.result.context.registry) (anchor := inventory.wordHeader.header) session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      inventory.wordHeader.header.function.context before (.global function) arguments outcome after

theorem word_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (value next : Core.Word) (flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word, .word, .bool]
      [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
  exact .cons (.data
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩)
    (.cons (.data
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
      (.cons (.data
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil))

theorem word_simple (value next : Core.Word) (flag : Bool) :
    ∀ item ∈ ([.word value, .word next, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .word value
  · exact .word next
  · exact .bool flag

theorem bool_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (value next flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.bool, .bool, .bool]
      [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
  exact .cons (.data
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩)
    (.cons (.data
      ⟨.bool next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool next⟩
      ⟨.bool next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool next⟩)
      (.cons (.data
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil))

theorem bool_simple (value next flag : Bool) :
    ∀ item ∈ ([.bool value, .bool next, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .bool value
  · exact .bool next
  · exact .bool flag

end Tests.SourceCoreMethodNamedScoped
