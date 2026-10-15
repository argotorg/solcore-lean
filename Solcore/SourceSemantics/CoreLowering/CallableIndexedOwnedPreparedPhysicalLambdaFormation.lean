import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts

/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model. -/
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

include profile prefixContext observed provenance allSlots callerReceipt in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) ∧
    CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember headers keys registry faults mapping world function
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.formation captured code support provenance owner initial packet
      profile prefixContext observed
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      (fun represented => represented) stored ordinary coercions
  have typed : RuntimeValueHasType world
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).runtime_hasType
      (registry := registry) related
  exact ⟨sourceTrace, nativeTrace, determined,
    ⟨.preparedOrdinary owner captured code (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed provenance allSlots callerReceipt⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
