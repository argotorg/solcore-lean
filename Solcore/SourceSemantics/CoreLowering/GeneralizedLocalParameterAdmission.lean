import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission

/-! A materialized read temporarily installs a read frame. Replacing that
frame by the actual child history recovers stable rows without pretending the
intermediate read frame was already stable. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {index reachedIndex : ProtectedStateTransition.Index}

def StableAway (saved : State headers keys index) (selected : Fin keys.length) : Prop :=
  ∀ i : Fin keys.length, keys[i.val].frameLocation ≠ keys[selected.val].frameLocation →
    ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (saved.rows i).authority.current (saved.rows i).authority.ghost metadata

/-- Actual read installation leaves all physically different rows stable. -/
theorem away_after_install (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableRows saved) {native : NativeFrame} {ghost : GhostFrame}
    (current : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost) :
    StableAway (install saved selected current) selected := by
  intro i different
  have native := CallableIndexedAuthorityPool.Pool.install_current saved selected i current
  have ghost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i current
  change ((install saved selected current).rows i).authority.current = _ at native
  change ((install saved selected current).rows i).authority.ghost = _ at ghost
  obtain ⟨metadata, history⟩ := stable i
  refine ⟨metadata, ?_⟩
  erw [native, ghost, if_neg different, if_neg different]
  exact history

/-- The child replaces every alias of its physical frame, while other rows
retain their actual histories from before the read. -/
theorem install_rows (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableAway saved selected) {next : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (install saved selected (.stable history)) := by
  intro i
  have current := CallableIndexedAuthorityPool.Pool.install_current saved selected i (.stable history)
  have actualGhost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i (.stable history)
  change ((install saved selected (.stable history)).rows i).authority.current = _ at current
  change ((install saved selected (.stable history)).rows i).authority.ghost = _ at actualGhost
  by_cases same : keys[i.val].frameLocation = keys[selected.val].frameLocation
  · refine ⟨metadata, ?_⟩
    erw [current, actualGhost, if_pos same, if_pos same]
    exact history
  · obtain ⟨oldMetadata, oldHistory⟩ := stable i same
    refine ⟨oldMetadata, ?_⟩
    erw [current, actualGhost, if_neg same, if_neg same]
    exact oldHistory

theorem after_parameters (saved : State headers keys index) (reached : State headers keys reachedIndex)
    (selected : Fin keys.length) (stable : StableAway saved selected)
    {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata)
    (frame : AdministrativePreserved index.mapping
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reachedIndex.mapping reachedIndex.store) :
    StableRows reached :=
  StableRows.after_administrative (install saved selected (.stable history)) reached
    (install_rows saved selected stable history) frame

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
