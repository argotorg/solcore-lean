import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory

/-! Actual restoration transports the history of the captured ready branch.
Its world, heap, registry and closure meanings are derived from the original
snapshot operation; no independent representation premise is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRestoredHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {publicArtifact : SourceCoreExecution.Artifact}
  {saved current : SourceCoreExecution.Session publicArtifact}
  {snapshot : SourceCoreExecution.Snapshot publicArtifact} {boundaryFuel : Nat}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {before after : SourceCoreIndexedSession.Session nativeArtifact}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : RecursiveNamedPublicFunctionHistory.Caller headers keys mapping world heap store}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}

/-- Reuse the captured branch's complete history at the actual restored public
session. Snapshot observation preserves all original handle payloads. -/
theorem restored_history
    (captured : saved.SnapshotAt boundaryFuel snapshot)
    (atSaved : saved.IndexedAt before) (restored : snapshot.restore = .ready current)
    (atCurrent : current.IndexedAt after)
    (history : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      before mapping world heap store caller entries) :
    RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      after mapping world heap store caller entries := by
  obtain ⟨actual, atActual, transported⟩ := captured.restored_indexed atSaved restored
  have same : actual = after := atActual.unique atCurrent
  cases same
  exact .restored history transported

/-- Ownership-checked restoration consumes the same original capture receipt.
The session performing the restore need not be the saved branch's latest state. -/
theorem restore_snapshot_history
    {restoring : SourceCoreExecution.Session publicArtifact}
    (captured : saved.SnapshotAt boundaryFuel snapshot)
    (atSaved : saved.IndexedAt before)
    (restored : restoring.restoreSnapshot snapshot = .ok (.ready current))
    (atCurrent : current.IndexedAt after)
    (history : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      before mapping world heap store caller entries) :
    RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      after mapping world heap store caller entries :=
  restored_history captured atSaved (SourceCoreExecution.Session.restoreSnapshot_ready restored)
    atCurrent history

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRestoredHistory
