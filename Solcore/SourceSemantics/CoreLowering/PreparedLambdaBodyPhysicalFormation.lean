import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts

/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyPhysicalFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open PreparedLambdaBodySupport (Support SourceOrigin PreparedAt)
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

/-- The history is read from the actual entered owning row. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

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
  obtain ⟨sourceTrace, nativeTrace, represented⟩ := CallableIndexedLambdaValues.formation
    captured code history (Program.ofChecked compiled.sourceProgram) heap ordinary coercions stored reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) represented
  exact ⟨sourceTrace, nativeTrace,
    (fun _ _ completed => Core.evaluation_deterministic completed nativeTrace),
    ⟨.preparedBranching owner captured code history support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) typed provenance allSlots callerReceipt⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyPhysicalFormation
