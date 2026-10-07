import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState

/-! Actual method-lambda parameter prefixes retain the genuine trait
principal's bundle and full Source seed. The original same-Code lambda
entry, actual reached pool and original Source admission remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The principal packet and all original ordered pool fields remain together. -/
def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (principal : SourceCoreGeneralFunctions.Function) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedOriginCanonicalState.carrier owner principal)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults) (sourceOrigin : SourceOrigin support history)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include observed leading sourceOrigin in
/-- Original Source prefix observations authenticate the reached row's own
full seed and the actual captured bundle, without an ordinary Header. -/
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
      entry.entry.reference⟩
  · exact entry.entry.environments
  · exact leading
  · exact sourceOrigin.metadata ▸ entry.nextHistory
  · exact entry.entry.read

include observed leading sourceOrigin in
/-- The independent measured prefix keeps its exact canonical spine and
read; the authentic method seed selects the reached row's own ghost. -/
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ reached := by
  obtain ⟨added, length, spine⟩ := entry.spine
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
      entry.reference⟩
  · exact entry.environments
  · exact leading
  · exact sourceOrigin.metadata ▸ entry.nextHistory
  · exact entry.read

variable (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include observed leading sourceOrigin beforeTyped argumentsTyped stable in
/-- The complete real Source entry is wrapped only with the authenticated
principal packet. Its Source receipt and stable rows are the original ones. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.principal.named)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.source_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable entry reached
  exact ⟨{ base.original with initial := ⟨reached,
    source_packet captured code history support sourceOrigin functions owner observed leading caller entry added length spine reached⟩ },
    base.source, base.rows⟩

include observed leading sourceOrigin beforeTyped argumentsTyped stable in
/-- Native admission uses the same actual Prefix allocation and reached pool;
Source body typing is established independently of the native body grade. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.principal.named)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) := by
  let base := CallableIndexedOwnedLambdaReadyContinuations.native_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable entry reached
  exact ⟨{ base.original with initial := ⟨reached,
    native_packet captured code history support sourceOrigin functions owner observed leading caller entry reached⟩ },
    base.source, base.rows⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries
