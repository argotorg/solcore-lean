import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals

/-! The original public fresh bootstrap and the public root startup share one
actual indexed Session. Successful bootstrap identifies its exact initialized
store/world, and startup retains those same indices. This covers one fresh
initial checkpoint completed at one supplied fuel; it does not replay native
execution or assume an initial owned pool, source heap or argument relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- The same facade Session ties actual bootstrap completion to the native
StartAt used by the public root consumer. The completion is returned for the
owned initialization producer, rather than replaced by a hypothetical store. -/
theorem at_started {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
    {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {nativeArtifact : Artifact} {nativeSession : Session nativeArtifact}
    {nativeCheckpoint : Checkpoint nativeArtifact} {root : Root recipe.compiled}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {inputFuel bootstrapFuel : Nat}
    {world : StoreTyping} {store : Store} {payloads : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
    (fresh : publicBootstrap.FreshAt)
    (ready : publicBootstrap.resume bootstrapFuel = .ready publicSession)
    (atSession : publicSession.IndexedAt nativeSession)
    (started : StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
      world store payloads encodedValues) :
    ∃ value,
      runStateful bootstrapFuel (.initial recipe.bootstrap [] []) =
        .done value (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      world = (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type ∧
      store = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      nativeSession.NativeAt
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      nativeSession.RegistryAt compiled.compatible.checked.staticRegistry ∧
      StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        (RecursiveNamedCatalogPreparedInitialization.store compiled) payloads encodedValues := by
  obtain ⟨indexedBootstrap, indexedSession, _atBootstrap, initial, sessionAt, accepted⟩ :=
    publicBootstrap.ready_indexed opened fresh ready
  have sameSession : indexedSession = nativeSession := sessionAt.unique atSession
  subst indexedSession
  obtain ⟨value, finalStore, completed, _success, booted⟩ :=
    Bootstrap.resume_ready_receipt indexedBootstrap bootstrapFuel accepted
  have actualCompletion := initial.native_done completed
  have initialized := RecursiveNamedCatalogPreparedInitialization.completed_store prepared actualCompletion
  rw [initialized.2] at actualCompletion
  have nativeAt := booted.native_at
  rw [initialized.2] at nativeAt
  have registryAt := booted.registry_at initial
  rw [Recipe.prepare_compiled prepared] at registryAt
  have sameState :
      world = (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type ∧
      store = RecursiveNamedCatalogPreparedInitialization.store compiled := by
    cases nativeSession
    exact ⟨started.state.1.symm.trans nativeAt.1, started.state.2.symm.trans nativeAt.2⟩
  have initializedStart : StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) payloads encodedValues := by
    simpa only [sameState.1, sameState.2] using started
  exact ⟨value, actualCompletion, sameState.1, sameState.2, nativeAt, registryAt, initializedStart⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
