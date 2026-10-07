import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries

/-! A method-produced lambda retains genuine trait Source authority and its
same-Code generic static body. Actual parameter prefixes construct the exact
principal-protocol index consumed by the shared family's strict body child. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- All original Code, Source authority, dictionary and body receipts remain
static. The genuine actual parameter admission supplies Source runtime. -/
structure Index where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  function : Dynamic.Closure
  scope : SourceCoreLocalCell.Scope
  administrative : Core.Context
  code : Code compiled.indexed function scope administrative
  history : History code
  support : Support code registry faults
  sourceOrigin : SourceOrigin support history
  leading : administrative[0]? = some support.principal.named.signature.parameterType
  escaped : faults .controlEscapedFunction code.compilation.internalReason
  syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    support.body.context function.source

/-- The whole same-Code compiler origin keeps its independent Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin (index.support.origin index.escaped) index.sourceRuntime

/-- The exact genuine method principal determines its captured packet protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) index.owner index.support.principal.named

/-- The bridge retains the same complete actual pool and principal packet. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) index.owner index.support.principal.named

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
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
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)

/-- Original Source prefix allocation and admission construct this index
internally at the same complete reached parameter pool. -/
def of_source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, function, scope, captured.administrative, code, history, support, sourceOrigin,
    leading, escaped, syntaxTree,
    (CallableIndexedOwnedMethodLambdaEntries.source_admitted_entry captured code history support sourceOrigin functions
      owner observed leading caller escaped beforeTyped argumentsTyped stable entry added length spine reached).source.runtime⟩

/-- Native prefix admission supplies its own genuine runtime receipt without
identifying the independent reflected Source grade with native execution. -/
def of_native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toContext functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, function, scope, captured.administrative, code, history, support, sourceOrigin,
    leading, escaped, syntaxTree,
    (CallableIndexedOwnedMethodLambdaEntries.native_admitted_entry captured code history support sourceOrigin functions
      owner observed leading caller escaped beforeTyped argumentsTyped stable entry reached).source.runtime⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- Only the strictly smaller shared-family body is consumed at this exact
authentic parameter index. The complete original entry output is retained. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  intro entry added length spine reached child strict outcome after trace
  let index := of_source_entry captured code history support sourceOrigin functions owner observed leading caller
    escaped beforeTyped argumentsTyped stable syntaxTree entry added length spine reached
  let actualEntry := CallableIndexedOwnedMethodLambdaEntries.source_admitted_entry captured code history support sourceOrigin functions
    owner observed leading caller escaped beforeTyped argumentsTyped stable entry added length spine reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include observed leading sourceOrigin beforeTyped argumentsTyped stable syntaxTree wellFormed in
/-- The original measured native prefix supplies this exact index and receives
the same restored body pool with its independently reconstructed Source grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions (Program.ofChecked compiled.sourceProgram) (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history support.body.toContext functions owner caller (support.body_origin escaped) budget := by
  intro entry reached child strict value finalStore completed
  let index := of_native_entry captured code history support sourceOrigin functions owner observed leading caller
    escaped beforeTyped argumentsTyped stable syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedMethodLambdaEntries.native_admitted_entry captured code history support sourceOrigin functions
    owner observed leading caller escaped beforeTyped argumentsTyped stable entry reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
