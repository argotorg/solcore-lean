import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries

/-! The real lambda parameter spine carries original captured global slots
into one actual canonical body entry. The reached pool is wrapped verbatim;
no old catalog authority or unrelated body entry is selected. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)

include observed in
/-- Ordered real parameter additions shift scope and captures by exactly the
same length, preserving every original selected named slot. -/
theorem globals_after_prefix {canonical : Environment} (added : Environment)
    (length : added.length = code.receipt.loweredParameters.length)
    (spine : canonical = added ++ captured.canonical) :
    Globals (headers := headers) owner callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) canonical := by
  intro header member
  rw [spine]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have index : code.receipt.loweredParameters.length + scope.length + callerPrefix + header.slot =
      added.length + (scope.length + callerPrefix + header.slot) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  simpa using observed.globals header member

variable (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)

include observed in
/-- The actual source parameter entry receives only the authentic slot proof. -/
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    (by simpa only [body.scope_eq, CallableIndexedOwnedLambdaInvocationBounds.source_entry] using globals_after_prefix captured code owner callerPrefix observed added length spine)

include observed in
/-- Native reflection uses the full spine already retained by its actual prefix. -/
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    (by
      obtain ⟨added, length, spine⟩ := entry.spine
      simpa only [body.scope_eq, CallableIndexedOwnedLambdaInvocationBounds.native_entry] using globals_after_prefix captured code owner callerPrefix observed added length spine)

/-- A strict canonical family is specialized to the exact source-produced
entry, then only its proof wrapper is forgotten at the actual body post. -/
theorem source_continuation_of_canonical (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (spine : entry.entry.canonical = added ++ captured.canonical)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner callerPrefix)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (source_entry captured code owner callerPrefix observed history inputs functions caller body
          entry added length spine reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.preserves_of_canonical functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry added length spine reached child strict)

/-- The original independently measured native prefix feeds its own canonical
family entry and receives the same base pool after the actual body. -/
theorem native_continuation_of_canonical (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner callerPrefix)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (native_entry captured code owner callerPrefix observed history inputs functions caller body entry reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.reflects_of_canonical functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry reached child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
