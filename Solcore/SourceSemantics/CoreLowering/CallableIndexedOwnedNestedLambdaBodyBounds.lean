import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries

/-! Authentic nested lambda bodies use the same imperative kernel and static
expression Tree. Named callees are closed by the proved named family; actual
parameter entries retain their own formation packets and reached pools. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedLambdaValues RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

section Body
variable (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (principalGlobals : principal.globals = compiled.indexed.base.globals.length)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {rank : Nat}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
    headers principal registry faults rank code)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction code.compilation.internalReason)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing in
/-- The original nested body Tree closes expressions internally. Its actual
input and returned formation packet contain exactly the real reached pools. -/
theorem preserves_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program
      (CallableRuntimeBodyStaticOrigins.lambda_nested (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) (program := program) code body bodyEscaped) size := by
  intro entry outcome after trace
  let readFuel := body.body.readFuel
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost size (fun child => ProtectedStateTransition.PreservesAt
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport (values := .initial compiled.compatible.checked)
            (indexed := compiled.indexed) headers principal registry faults rank)
          rank principal headers code.compilation readFuel function.source context function.evidence
          code.compilation.solvedRequirements code.reasonAt) faults child) := by
    intro context valid child within
    rw [body.compilation] at valid ⊢
    apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
      owner principal prefixZero profile complete principalGlobals slots body.source
      extension faithful observations functionTypes function.evidence body.body.unique owners bodyUninitialized bodyMissing
      sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      valid.ledger valid.runtime size child within
    intro callee member smaller _strict
    exact CallableIndexedOwnedNestedNamedFamilyClosure.preserves_at owner prefixZero profile complete globals slots sameLayouts
      extension faithful observations functionTypes owners uninitialized missing escaped ranks profiles smaller callee member
  exact CallableRuntimeBodyKernel.Stateful.BodyFor.preserves_sized
    (body := body.toKernel) (functions := CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    (definitions := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (extension := extension) (program := program) (faithful := faithful) (observations := observations)
    (escapedFault := bodyEscaped) (extend := fun valid extended => valid.extend extended)
    (runtimeOf := fun valid => valid)
    (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
    (producer := CallableIndexedOwnedNestedCanonicalState.markedProducer owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (acquire := fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)
    (stateTransport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner principal)
    (stateBindings := CallableIndexedOwnedNestedCanonicalState.bindings owner principal)
    size size (Nat.le_refl _) expressions
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.initial entry.gate trace

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing in
/-- The same native body proof returns its independent Source grade and the
actual post state, including every ordered record produced by callees. -/
theorem reflects_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program
      (CallableRuntimeBodyStaticOrigins.lambda_nested (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) (program := program) code body bodyEscaped) size := by
  intro entry value finalStore completed
  let readFuel := body.body.readFuel
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below size (fun child => ProtectedStateTransition.ReflectsAt
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport (values := .initial compiled.compatible.checked)
            (indexed := compiled.indexed) headers principal registry faults rank)
          rank principal headers code.compilation readFuel function.source context function.evidence
          code.compilation.solvedRequirements code.reasonAt) faults child) := by
    intro context valid child strict
    rw [body.compilation] at valid ⊢
    apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
      owner principal prefixZero profile complete principalGlobals slots body.source
      extension faithful observations functionTypes function.evidence bodyUninitialized bodyMissing
      sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
      valid.ledger valid.runtime size child (Nat.le_of_lt strict)
    intro callee member smaller _strict
    exact CallableIndexedOwnedNestedNamedFamilyClosure.reflects_at owner prefixZero profile complete globals slots sameLayouts
      extension faithful observations functionTypes uninitialized missing escaped ranks profiles smaller callee member
  exact CallableRuntimeBodyKernel.Stateful.BodyFor.reflects_sized
    (body := body.toKernel) (functions := CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    (definitions := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (extension := extension) (program := program) (faithful := faithful) (observations := observations)
    (functionTypes := functionTypes) (escapedFault := bodyEscaped)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
    (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
    (producer := CallableIndexedOwnedNestedCanonicalState.markedProducer owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (acquire := fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner principal
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)
    (stateTransport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner principal)
    (stateBindings := CallableIndexedOwnedNestedCanonicalState.bindings owner principal)
    size size (Nat.le_refl _) expressions
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.initial entry.gate completed
end Body

section Continuation
variable (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  (principalGlobals : principal.globals = compiled.indexed.base.globals.length)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {rank : Nat}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
    headers principal registry faults rank code)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction code.compilation.internalReason)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (sourceSeed : history.metadata = CallableIndexedNamedGeneration.state principal.named)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing observed sourceSeed in
/-- A strict Source invocation child uses its authentic parameter Entry and
actual reached pool. All expression and named body meanings are closed here. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      owner caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget := by
  apply CallableIndexedOwnedLambdaNestedEntries.source_continuation_of_nested
    captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    owner principal observed body.administrative sourceSeed caller
    (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget
  intro entry added length spine reached child _strict
  exact preserves_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles principal principalGlobals code body bodyUninitialized bodyMissing bodyEscaped child
    (CallableIndexedOwnedLambdaNestedEntries.source_entry captured code history inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner principal observed body.administrative sourceSeed
      caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) entry added length spine reached)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles principalGlobals body bodyUninitialized bodyMissing observed sourceSeed in
/-- Native invocation reflection consumes its own complete measured Prefix and
retains the independent Source grade and the same body-produced final pool. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      owner caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget := by
  apply CallableIndexedOwnedLambdaNestedEntries.native_continuation_of_nested
    captured code history inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
    owner principal observed body.administrative sourceSeed caller
    (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) budget
  intro entry reached child _strict
  exact reflects_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles principal principalGlobals code body bodyUninitialized bodyMissing bodyEscaped child
    (CallableIndexedOwnedLambdaNestedEntries.native_entry captured code history inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner principal observed body.administrative sourceSeed
      caller (CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested code inputs body bodyEscaped) entry reached)
end Continuation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds
