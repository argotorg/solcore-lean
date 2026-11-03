import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts

/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model.
The formation copies the captured cells, and the copies keep every global slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport (Support SourceOrigin PreparedAt)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : PreparedAt code support)
  (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
  (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
    support.caller function.context function.evidence))

open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (history_at source_origin reference_index)

include packet profile prefixContext observed provenance allSlots callerReceipt in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. The member is
the formed closure over the copies of its captured cells. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code (history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember headers keys registry faults formed.finalMap
        formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  let history := history_at captured code support owner initial packet
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots provenance)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated,
    ⟨.preparedOrdinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture provenance formed.captured)
      (allSlots.of_slots formed.slots) callerReceipt⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
