import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries

/-! The real lambda parameter spine retains its lexical principal's original
named Source seed, captured bundle and canonical globals. Both Source and
native entry factories use their own actual reached parameter pools. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames RecursiveNamedLambdaFormationHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (history : History code) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = nativePrefix (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)

include observed prefixContext sourceSeed in
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ reached := by
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner principal reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
      entry.entry.reference⟩
  · exact entry.entry.environments
  · rw [prefixContext]
    rfl
  · exact sourceSeed ▸ entry.nextHistory
  · exact entry.entry.read

include observed prefixContext sourceSeed in
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ reached := by
  obtain ⟨added, length, spine⟩ := entry.spine
  apply CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner principal reached
  · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length spine,
      entry.reference⟩
  · exact entry.environments
  · rw [prefixContext]
    rfl
  · exact sourceSeed ▸ entry.nextHistory
  · exact entry.read

include observed prefixContext sourceSeed in
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyNestedEntries.wrap functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    (by
      change CallableIndexedOwnedNestedCanonicalState.Packet owner principal
        ⟨body.origin.scope, entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ reached
      rw [body.scope_eq]
      exact source_packet captured code history inputs functions owner principal observed prefixContext sourceSeed caller entry added length spine reached)

include observed prefixContext sourceSeed in
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyNestedEntries.wrap functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    (by
      change CallableIndexedOwnedNestedCanonicalState.Packet owner principal
        ⟨body.origin.scope, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ reached
      rw [body.scope_eq]
      exact native_packet captured code history inputs functions owner principal observed prefixContext sourceSeed caller entry reached)

include observed prefixContext sourceSeed in
/-- The strict family callback is applied only to the genuine Source-produced
parameter entry, with its actual spine and full reached pool. -/
theorem source_continuation_of_nested (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (spine : entry.entry.canonical = added ++ captured.canonical)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (source_entry captured code history inputs functions owner principal observed prefixContext sourceSeed
          caller body entry added length spine reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached child strict
  exact CallableIndexedOwnedBodyNestedEntries.preserves_of_nested functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry added length spine reached child strict)

include observed prefixContext sourceSeed in
/-- Native reflection uses its own real measured prefix. The independent
Source body grade and the actual returned pool survive projection. -/
theorem native_continuation_of_nested (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      RecursiveNamedBoundedContracts.Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (native_entry captured code history inputs functions owner principal observed prefixContext sourceSeed
          caller body entry reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict
  exact CallableIndexedOwnedBodyNestedEntries.reflects_of_nested functions owner principal
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry reached child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
