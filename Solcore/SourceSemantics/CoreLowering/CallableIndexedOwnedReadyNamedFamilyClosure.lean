import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! Authentic named compiler profiles close their ready bodies through the
existing measured family. The original expression support fold supplies named
ordinary and direct calls at actual canonical parameter receipts. Source
syntax, dictionaries, compiler contexts and runtime ledgers remain genuine
static inputs; no expression or body execution law is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (compilation : CallableIndexedOwnedFunctionValues.Header compiled program → SourceCoreFunctions.Context)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- This is the original full-evidence runtime compiler certificate family,
at each header's actual compilation context and read fuel. -/
abbrev certificates (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (context : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (some header.function.evidence)
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt

/-- The index retains the exact compiler profile, independently typed Syntax
and real Source runtime receipt at that profile's original parameter context. -/
abbrev Index := CallableIndexedOwnedNamedReadyFamilyReceipts.Index
  (headers := headers) (registry := registry) (faults := faults) (certificates := certificates (headers := headers) compilation)
  (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true

private def base_origin (index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults :=
  CallableRuntimeBodyStaticOrigins.named (header := index.header)
    (certificates := certificates (headers := headers) compilation index.header) (expressionSyntax := expressionSyntax index.header)
    (diagnosticPolicy := .reachable) true index.profile index.escaped

/-- Each origin retains the complete actual compiler and Source body receipt. -/
abbrev origin (index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation) :=
  CallableIndexedOwnedNamedReadyFamilyReceipts.origin true index

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (prefixMatches : ∀ header, header ∈ headers → (compilation header).administrativePrefix = owner.key.capturePrefix + 1)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates (headers := headers) compilation) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

private def producer (index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation) :
    ProtectedStateTransition.MarkedAllocation.Producer (body_protocol (headers := headers) owner)
      (origin compilation index).layouts (origin compilation index).frameLayout
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) := by
  change ProtectedStateTransition.MarkedAllocation.Producer (body_protocol (headers := headers) owner)
    index.header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  exact (sameLayouts index.header index.member).symm ▸
    CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer (body_protocol (headers := headers) owner)
      second compiled.indexed.ancestry.layout.frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation) (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer compilation functions owner sameLayouts index).toOrdinary location native := by
  exact ready_layout owner (sameLayouts index.header index.member)
    (CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

private def bindings := CallableIndexedOwnedCanonicalState.bindings (headers := headers) owner (owner.key.capturePrefix + 1)
private def transport := CallableIndexedOwnedCanonicalState.administrativeTransport (headers := headers) owner (owner.key.capturePrefix + 1)

/-- Genuine typed Source sites and actual transfer receipts build the finite
catalog inputs internally at this exact strengthened origin. -/
def inputs (index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation) :=
  CallableIndexedOwnedBodyReadyCatalog.inputs (bridge (headers := headers) owner)
    (base_origin compilation index) index.sourceRuntime (bindings (headers := headers) owner) wellFormed

include extension faithful observations functionTypes wellFormed owners sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- The same measured family closes arbitrary authentic named bodies. Its
only expression children are proved internally by the original support fold. -/
theorem preserves_at (size : Nat) : ∀ index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation,
    CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) owner)
      (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (inputs compilation owner wellFormed index).facts functions program (origin compilation index) size := by
  apply CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at
    (origin compilation) functions program observations
    (fun _ => body_protocol (headers := headers) owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer compilation functions owner sameLayouts) (acquire compilation functions owner sameLayouts)
    (fun _ => transport (headers := headers) owner) (fun _ => bindings (headers := headers) owner)
    (fun _ => readiness (bridge (headers := headers) owner)) (inputs compilation owner wellFormed) ?_ ?_ size
  · intro index context valid budget child within below
    apply CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at (bridge (headers := headers) owner) _
    change CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy
        (CallableIndexedOwnedCallerProtocol.canonical (headers := headers) owner (owner.key.capturePrefix + 1)))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context index.header.function.evidence index.header.function.source (certificates (headers := headers) compilation index.header context) faults child
    rw [← prefixMatches index.header index.member]
    exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.preserves_at_runtime
      (certificates := certificates (headers := headers) compilation) (compilation := compilation index.header) (fuel := index.header.readFuel)
      functions extension faithful observations functionTypes owner index.header.function.evidence
      wellFormed valid.2 valid.1.covers index.header.unique owners valid.1.runtime.1
      (uninitialized index.header index.member) (missing index.header index.member) sameLayouts escaped profiles syntaxTrees
      valid.1.ledger valid.1.runtime budget child within below
  · intro index budget children
    exact CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits (bridge (headers := headers) owner)
      (base_origin compilation index) index.sourceRuntime (bindings (headers := headers) owner) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer compilation functions owner sameLayouts index) (acquire compilation functions owner sameLayouts index)
      (transport (headers := headers) owner) budget children

include extension faithful observations functionTypes wellFormed sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- Native body and expression grades keep their original strict children;
the same measured family returns an independent Source trace and actual post. -/
theorem reflects_at (size : Nat) : ∀ index : Index (headers := headers) (registry := registry) (faults := faults)
    (expressionSyntax := expressionSyntax) compilation,
    CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) owner)
      (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (inputs compilation owner wellFormed index).facts functions program (origin compilation index) size := by
  apply CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at
    (origin compilation) functions program observations
    (fun _ => body_protocol (headers := headers) owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer compilation functions owner sameLayouts) (acquire compilation functions owner sameLayouts)
    (fun _ => transport (headers := headers) owner) (fun _ => bindings (headers := headers) owner)
    (fun _ => readiness (bridge (headers := headers) owner)) (inputs compilation owner wellFormed) ?_ ?_ size
  · intro index context valid budget child within below
    apply CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at (bridge (headers := headers) owner) _
    change CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy
        (CallableIndexedOwnedCallerProtocol.canonical (headers := headers) owner (owner.key.capturePrefix + 1)))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context index.header.function.evidence index.header.function.source (certificates (headers := headers) compilation index.header context) faults child
    rw [← prefixMatches index.header index.member]
    exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.reflects_at_runtime
      (certificates := certificates (headers := headers) compilation) (compilation := compilation index.header) (fuel := index.header.readFuel)
      functions extension faithful observations functionTypes owner index.header.function.evidence
      wellFormed valid.2 valid.1.covers index.header.unique
      (uninitialized index.header index.member) (missing index.header index.member) sameLayouts escaped profiles syntaxTrees
      valid.1.ledger valid.1.runtime budget child within below
  · intro index budget children
    exact CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits (bridge (headers := headers) owner)
      (base_origin compilation index) index.sourceRuntime (bindings (headers := headers) owner) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer compilation functions owner sameLayouts index) (acquire compilation functions owner sameLayouts index)
      (transport (headers := headers) owner) budget functionTypes children

variable {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates (headers := headers) compilation) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) argumentsPool header arguments)

include extension faithful observations functionTypes wellFormed owners sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- The actual named parameter receipt consumes the internally closed family
and retains full semantic fields and admission at the same returned pool. -/
theorem parameter_preserves (member : header ∈ headers) {size : Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner true receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  exact CallableIndexedOwnedNamedReadyFamilyReceipts.parameter_preserves true functions owner receipt wellFormed
    member (syntaxTrees header member) (budget := size + 1)
    (fun index child _strict => preserves_at compilation functions owner extension faithful observations functionTypes
      wellFormed owners sameLayouts prefixMatches uninitialized missing escaped profiles syntaxTrees child index)
    (Nat.lt_succ_self size) trace

include extension faithful observations functionTypes wellFormed sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- The same actual native completion yields its independent Source grade
from the internally closed family and the unchanged rich parameter result. -/
theorem parameter_reflects (member : header ∈ headers) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      CallableIndexedOwnedNamedReadyContinuations.ResultAt functions owner true receipt wellFormed
        outcome after value finalStore finalMap finalWorld := by
  exact CallableIndexedOwnedNamedReadyFamilyReceipts.parameter_reflects true functions owner receipt wellFormed
    member (syntaxTrees header member) (budget := size + 1)
    (fun index child _strict => reflects_at compilation functions owner extension faithful observations functionTypes
      wellFormed sameLayouts prefixMatches uninitialized missing escaped profiles syntaxTrees child index)
    (Nat.lt_succ_self size) completed

include extension faithful observations functionTypes wellFormed owners sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- Named call body callbacks are closed internally at genuine parameter
receipts; there is no external expression or body meaning premise. -/
theorem source_bodies (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget :=
  CallableIndexedOwnedNamedReadyFamilyReceipts.source_bodies (functions := functions) (owner := owner)
    (runtime := true) wellFormed member (syntaxTrees header member)
    (fun index child _strict => preserves_at compilation functions owner extension faithful observations functionTypes
      wellFormed owners sameLayouts prefixMatches uninitialized missing escaped profiles syntaxTrees child index)

include extension faithful observations functionTypes wellFormed sameLayouts prefixMatches
  uninitialized missing escaped profiles syntaxTrees in
/-- Native callbacks retain the original prefix and saved caller write while
using the same internally closed actual body family. -/
theorem native_bodies (member : header ∈ headers) (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true)
      wellFormed header budget :=
  CallableIndexedOwnedNamedReadyFamilyReceipts.native_bodies (functions := functions) (owner := owner)
    (runtime := true) wellFormed member (syntaxTrees header member)
    (fun index child _strict => reflects_at compilation functions owner extension faithful observations functionTypes
      wellFormed sameLayouts prefixMatches uninitialized missing escaped profiles syntaxTrees child index)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedFamilyClosure
