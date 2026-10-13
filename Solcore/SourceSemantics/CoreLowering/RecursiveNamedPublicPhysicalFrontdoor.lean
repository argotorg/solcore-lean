import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage

/-! Actual public startup needs Source attribution only for its selected root.
Complete physical method slots are retained separately from ordinary semantic
headers; the whole-root coverage API remains a specialization. -/
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

/-- Recover the actual public start using only its selected root. A static
selector may retain additional Source admission at the exact returned Header;
no coverage of unrelated roots or body execution is required. -/
theorem recover_start_at_with
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (admitted : Root compiled →
      CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Prop)
    (select : ∀ root : Root compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) =
        some ((Recipe.prepare_compiled prepared).symm ▸ root) →
      ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header ∧
        admitted root header)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ request : Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store,
      admitted request.root request.header := by
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
      obtain ⟨header, selectedRoot, admission⟩ := select root started.selected
      obtain ⟨rawD, function, sourceAt⟩ := (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts
        header selectedRoot.member
      exact ⟨⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
        atCheckpoint, started, selectedRoot, sourceAt⟩, admission⟩


/-- A Header selector for the actual first matching public root suffices to
recover the same start receipt used by existing public continuations. -/
theorem recover_start_at
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (select : ∀ root : Root compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) =
        some ((Recipe.prepare_compiled prepared).symm ▸ root) →
      ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    Nonempty (Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store) := by
  obtain ⟨request, _⟩ := recover_start_at_with prepared inputs rows atRecipe native atSession
    (fun _ _ => True) (fun root selected => by
      obtain ⟨header, selectedRoot⟩ := select root selected
      exact ⟨header, selectedRoot, True.intro⟩) accepted
  exact ⟨request⟩


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
  apply recover_start_at prepared inputs rows atRecipe native atSession _ accepted
  intro root selected
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  exact RecursiveNamedPublicRootCoverage.selection_of_recipe prepared
    (List.mem_of_find?_eq_some selected) coverage

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
