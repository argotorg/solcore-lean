import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedLambdaBodyBounds

/-! Closed body continuations are a separate specialization of the selected
indirect interface. They apply the existing named/literal body family to the
same authentic future captures and actual ordered argument post. The shared
mixed-origin closer can instead supply its strict IH through the generic
selected interface; this module does not enlarge that existing family's grammar. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
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


open CallableIndexedOwnedIndirectExpressionHeads
universe u
variable
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {ids : List ExpressionId}
  {callerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (sameOwner : closure.owner = owner) (prefixOne : closure.callerPrefix = 1)
  (principalGlobals : closure.support.1.globals = compiled.indexed.base.globals.length)
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (closure.code.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((closure.code.reasonAt id).add tag))
  (bodyEscaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles sameOwner prefixOne principalGlobals bodyUninitialized bodyMissing in
/-- Each real argument post obtains a closed Source continuation at its exact
parameter Entry and body. The authentic selected owner and full captured
canonical prefix are preserved through the actual argument effects. -/
theorem source_continuations (budget : Nat) :
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure bodyEscaped bridge initial budget := by
  subst owner
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    parameterArguments middleHeaps sourceCaptures frame metadata related sourceArgumentsSize sourceArguments
  let future := closure.extend maps worlds
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers future.owner.key.locations 1 future.scope future.captured.canonical future.owner.key.frameLocation := by
    have same : future.callerPrefix = 1 := prefixOne
    simpa only [same] using future.globals
  exact CallableIndexedOwnedNestedLambdaBodyBounds.source_continuation
    closure.owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles future.support.1 principalGlobals
    future.captured future.code future.history future.inputs future.support.2.2.receipt
    bodyUninitialized bodyMissing bodyEscaped observed future.origin.historyMetadata (bridge.pool argumentState) budget

include prefixZero complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles sameOwner prefixOne principalGlobals bodyUninitialized bodyMissing in
/-- Native continuation reflection consumes the actual Prefix and reached
body pool, keeping independent Source grades and exact final restoration. -/
theorem native_continuations (budget : Nat) :
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure bodyEscaped bridge initial budget := by
  subst owner
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    parameterArguments middleHeaps sourceCaptures frame metadata related sourceArgumentsSize sourceArguments
  let future := closure.extend maps worlds
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers future.owner.key.locations 1 future.scope future.captured.canonical future.owner.key.frameLocation := by
    have same : future.callerPrefix = 1 := prefixOne
    simpa only [same] using future.globals
  exact CallableIndexedOwnedNestedLambdaBodyBounds.native_continuation
    closure.owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles future.support.1 principalGlobals
    future.captured future.code future.history future.inputs future.support.2.2.receipt
    bodyUninitialized bodyMissing bodyEscaped observed future.origin.historyMetadata (bridge.pool argumentState) budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
