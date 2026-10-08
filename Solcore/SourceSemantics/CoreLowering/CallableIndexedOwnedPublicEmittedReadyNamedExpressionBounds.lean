import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds

/-! The actual public compiler traversals supply their own interpreted profile
receipts inside the ordinary named runtime endpoint. Independent Source Syntax,
real child compilation receipts and concrete local diagnostic facts remain
static inputs. The existing closed named family supplies all body semantics. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicEmittedReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicReadyNamedExpressionBounds (PublicReceipt compilation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable {faults : FunctionCalls.FaultRep}

/-- Genuine static inputs are tied to the actual public Header and requested
only at real ordinary parameter entries. They contain no interpreted output
predicate, profile provider or expression/body execution law. -/
structure StaticInputs (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header) where
  tracked : Bool
  children : CallableIndexedOwnedNamedPublicProfileExtraction.SitesFor
    (header := header) (headers := headers) (registry := registry) (expressionSyntax := expressionSyntax)
    issued.prepared compilation functions owner tracked
  localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
    (actualEntry : RecursiveNamedCatalogInvocationBounds.BodyState
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost),
    EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (ordinary : owner.key.capturePrefix = 0)
  (publicReceipts : ∀ header, header ∈ headers → PublicReceipt header)
  (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (staticInputs : ∀ header (member : header ∈ headers),
    StaticInputs (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults)
      (expressionSyntax := expressionSyntax) header (publicReceipts header member))
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include complete publicReceipts staticInputs in
/-- Each reached Header's authentic producer interprets its own returned plan
and constructs the original static profile witness internally. -/
theorem interpreted_outputs : ∀ header, header ∈ headers →
    CallableIndexedOwnedNamedPublicProfileExtraction.InterpretedReceiptsFor
      (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax)
      (header := header) compilation functions owner := by
  intro header member
  let issued := publicReceipts header member
  let inputs : StaticInputs (functions := functions) (owner := owner) (headers := headers)
      (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) header issued :=
    staticInputs header member
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  let sites := CallableIndexedOwnedNamedPublicProfileExtraction.policy_inputs
    issued.prepared issued.aligned compilation (inputs.children actualEntry)
  exact CallableIndexedOwnedNamedEmittedProfileExtraction.interpreted_at
    issued.accepted issued.prepared issued.aligned issued.nativeMember compilation functions owner complete
    actualEntry sites (inputs.localReceipts actualEntry)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.preserves_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped complete staticInputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedPublicReadyNamedExpressionBounds.reflects_at_runtime
    (callerCompilation := callerCompilation) (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped
    (interpreted_outputs (functions := functions) (owner := owner) (complete := complete)
      (publicReceipts := publicReceipts) (staticInputs := staticInputs)) syntaxTrees
    sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicEmittedReadyNamedExpressionBounds
