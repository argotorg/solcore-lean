import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations

/-! Unrestricted ordinary static support enters the existing actual lambda
parameter producers through its genuine cached Header and complete Source seed.
Full real Entry/Prefix, raw Source receipt and reached ordered pool stay original.
The function model remains a parameter throughout these finite adapters. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The genuine nested Header packet projects and restores the same pool. -/
def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner caller

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
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include observed prefixContext sourceOrigin in
/-- The actual Source Entry and spine select the original Header packet. -/
theorem source_packet
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached :=
  CallableIndexedOwnedLambdaNestedEntries.source_packet captured code history support.body.toContext
    functions owner support.caller observed prefixContext sourceOrigin.metadata caller entry added length spine reached

include observed prefixContext sourceOrigin in
/-- The independent native Prefix keeps its real spine, read and full seed. -/
theorem native_packet
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached :=
  CallableIndexedOwnedLambdaNestedEntries.native_packet captured code history support.body.toContext
    functions owner support.caller observed prefixContext sourceOrigin.metadata caller entry reached

variable (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- The complete real Source entry is wrapped only with the authenticated
Header packet. Its Source receipt and stable rows are the original ones. -/
def source_admitted_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.caller)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable support.caller observed prefixContext sourceOrigin.metadata
    entry added length spine reached

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- Native admission uses the same actual Prefix allocation and reached pool;
Source body typing is established independently of the native body grade. -/
def native_admitted_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry (bridge (headers := headers) owner support.caller)
      (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := (support.body_origin escaped).origin) (functions := functions) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history support.body.toContext functions owner caller (support.body_origin escaped)
    beforeTyped argumentsTyped stable support.caller observed prefixContext sourceOrigin.metadata entry reached

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- The Source adapter retains exactly the producer's full reached pool. -/
theorem source_pool
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    (source_admitted_entry captured code history support sourceOrigin functions owner observed prefixContext caller
      escaped beforeTyped argumentsTyped stable entry added length spine reached).original.initial.val = reached := rfl

include observed prefixContext sourceOrigin beforeTyped argumentsTyped stable in
/-- Native packaging retains the independent Prefix producer's same pool. -/
theorem native_pool
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    (native_admitted_entry captured code history support sourceOrigin functions owner observed prefixContext caller
      escaped beforeTyped argumentsTyped stable entry reached).original.initial.val = reached := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
