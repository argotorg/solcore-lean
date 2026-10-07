import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedReadyContinuations

/-! Genuine lambda code, complete captured compiler seed and original body
Syntax construct a dependent family index at the actual parameter entry.
Its strict child is consumed through the original pointwise continuation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyFamilyReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Code and body alignments remain original receipts. Runtime validity is
independent raw Source authority, supplied by the actual parameter admission. -/
structure Index where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  principal : CallableIndexedOwnedFunctionValues.Header compiled program
  function : Dynamic.Closure
  scope : SourceCoreLocalCell.Scope
  administrative : Core.Context
  code : Code compiled.indexed function scope administrative
  history : History code
  inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code
  body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults
  prefixContext : administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal
  sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named
  syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType
  sourceRuntime : Dynamic.SourceRuntimeValid program body.origin.context body.origin.function.source

/-- The whole compiler origin is retained, with its genuine Source domain. -/
def origin (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  source_origin index.body.origin index.sourceRuntime

/-- This exact captured principal and owner determine the stronger protocol. -/
def body_protocol (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) index.owner index.principal

/-- The bridge keeps the complete actual pool beside the principal packet. -/
def bridge (index : Index (keys := keys) (registry := registry) (faults := faults)) :=
  CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) index.owner index.principal

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) (program := program) principal)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  (syntaxTree : GenericImperativeMatch.Syntax body.origin.function.source body.origin.expressionSyntax
    body.origin.context (.statements true body.origin.function.body) body.origin.function.resultType)

/-- The real Source prefix supplies its runtime receipt. No arbitrary closure
representation or external origin-selection function is used. -/
def of_source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, principal, function, scope, captured.administrative, code, history, inputs, body,
    prefixContext, sourceSeed, syntaxTree,
    (CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry captured code history inputs functions owner caller body
      beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry added length spine reached).source.runtime⟩

/-- The measured native prefix retains the same compiler/body receipts and
supplies independent raw Source admission at its own reached pool. -/
def of_native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    Index (keys := keys) (registry := registry) (faults := faults) :=
  ⟨owner, principal, function, scope, captured.administrative, code, history, inputs, body,
    prefixContext, sourceSeed, syntaxTree,
    (CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry captured code history inputs functions owner caller body
      beforeTyped argumentsTyped stable principal observed prefixContext sourceSeed entry reached).source.runtime⟩

variable (wellFormed : ProgramWellFormed program)

include wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- Each authentic actual Source parameter entry constructs its index and
uses only the strict shared-family child in that index's exact protocol. -/
theorem source_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions program (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length spine reached child strict outcome after trace
  let index := of_source_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry added length spine reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.source_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry added length spine reached
  have ready := below index child strict
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.preserves_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

include wellFormed beforeTyped argumentsTyped stable observed prefixContext sourceSeed syntaxTree in
/-- The original measured prefix constructs the same static index directly;
reflection preserves the independently reconstructed Source body grade. -/
theorem native_continuation (budget : Nat)
    (below : ∀ index : Index (keys := keys) (registry := registry) (faults := faults),
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) index)
          (readiness (bridge (headers := headers) index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin index).function.source (origin index).expressionSyntax)
          functions program (origin index))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict value finalStore completed
  let index := of_native_entry captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed syntaxTree entry reached
  let actualEntry := CallableIndexedOwnedLambdaNestedReadyContinuations.native_admitted_entry
    captured code history inputs functions owner caller body beforeTyped argumentsTyped stable
    principal observed prefixContext sourceSeed entry reached
  have ready := below index child strict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, returned, related, _post⟩ :=
    CallableIndexedOwnedSourceBodyReadyBounds.reflects_at
      (CallableIndexedOwnedLambdaNestedReadyContinuations.bridge (headers := headers) owner principal)
      actualEntry.source.runtime wellFormed syntaxTree ready actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaReadyFamilyReceipts
