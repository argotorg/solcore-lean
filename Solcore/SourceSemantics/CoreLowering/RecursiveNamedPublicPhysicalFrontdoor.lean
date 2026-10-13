import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage

/-! Actual public startup uses only public-entry Source coverage. Complete
physical method slots are retained separately from ordinary semantic headers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

private theorem start_at_state {artifact : Artifact} {session : Session artifact}
    {world actualWorld : StoreTyping} {store actualStore : Store}
    (native : session.NativeAt world store) (state : SessionState session actualWorld actualStore) :
    actualWorld = world ∧ actualStore = store := by
  cases session
  rename_i authority currentWorld currentStore stored environmentTyped registry values owner sourcePrefix
  change currentWorld = world ∧ currentStore = store at native
  change currentWorld = actualWorld ∧ currentStore = actualStore at state
  exact ⟨state.1.symm.trans native.1, state.2.symm.trans native.2⟩

/-- Recover the actual selected root and current native input state for a
following public call. The caller can then retain its exact Source arguments
when invoking the public continuation theorem. -/
theorem recover_start_covered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    (coverage : RecursiveNamedPublicRootCoverage.Coverage
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers rows))
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    Nonempty (Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store) := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  rcases publicArtifact with ⟨publicCompiled, opened⟩
  cases opened with
  | empty selected => exact False.elim atSession
  | indexed actualRecipe selected actualArtifact recipeAt =>
      rcases publicSession with ⟨actualSession⟩
      rcases atSession with ⟨rfl, sameSession⟩
      have same : actualSession = session := eq_of_heq sameSession
      subst actualSession
      obtain ⟨foundRecipe, foundArtifact, foundSession, checkpoint,
          _openedAt, atFound, atCheckpoint, startEq⟩ :=
        SourceCoreExecution.Session.start_indexed (compiled := publicCompiled)
          (checkpoint := publicCheckpoint) rfl accepted
      have artifactEq : actualArtifact = foundArtifact := atFound.1
      cases artifactEq
      have sessionEq : session = foundSession := eq_of_heq atFound.2
      cases sessionEq
      obtain ⟨currentRecipe, root, actualWorld, actualStore, payloads, encodedValues, started⟩ :=
        RecursiveNamedPublicStartMeaning.actual_start session startEq
      have recipeEq : currentRecipe = recipe := by
        cases actualArtifact
        exact started.recipe_eq.symm.trans atRecipe
      subst currentRecipe
      obtain ⟨worldEq, storeEq⟩ := start_at_state native started.state
      subst actualWorld
      subst actualStore
      obtain ⟨header, selectedRoot⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe prepared
        (List.mem_of_find?_eq_some started.selected) coverage
      obtain ⟨rawD, function, sourceAt⟩ := (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts
        header selectedRoot.member
      exact ⟨⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
        atCheckpoint, started, selectedRoot, sourceAt⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
