import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction

/-! Genuine public Header receipts and explicitly interpreted static compiler
outputs supply proof-local profile providers to the already closed named
family. Ordinary/direct calls retain actual Source typing and runtime ledgers;
residual compiler diagnostics and independent Syntax remain static inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

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

/-- The complete actual public compiler packet retains its original cached
code, metadata, independent dictionary and checked native entry membership. -/
structure PublicReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts
  nativeMember : nativeEntry ∈ compiled.indexed.entries

/-- This is the actual named compiler context, including its fixed bundle slot. -/
def compilation (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) : SourceCoreFunctions.Context :=
  CallableIndexedNamedGeneration.context compiled.indexed header.named

/-- The genuine public cached code and support feed the original extraction at
the exact ordinary parameter entry. Returned diagnostics remain that receipt's. -/
theorem extract_at (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) (issued : PublicReceipt header)
    {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (entry : RecursiveNamedCatalogInvocationBounds.BodyState
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
      administrative actualContext actual ξ frameLocation current ghost)
    {tracked : Bool}
    (sites : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true tracked .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  CallableIndexedOwnedNamedPublicProfileExtraction.extract_at issued.accepted issued.prepared issued.aligned
    issued.nativeMember compilation functions owner complete entry sites

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
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
  (outputs : ∀ header, header ∈ headers →
    CallableIndexedOwnedNamedPublicProfileExtraction.InterpretedReceiptsFor
      (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax)
      (header := header) compilation functions owner)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include publicReceipts in
/-- Full layouts come from the real public Header construction. -/
theorem same_layouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts :=
  fun header member => (publicReceipts header member).aligned.layouts

include ordinary in
/-- The original named compiler's administrative prefix is the actual bundle
slot. Genuine ordinary capture prefix supplies the family boundary directly. -/
theorem prefix_matches : ∀ header, header ∈ headers →
    (compilation header).administrativePrefix = owner.key.capturePrefix + 1 := by
  intro header _member
  simp only [ordinary]
  rfl

include ordinary catalog outputs in
/-- Interpreted static output receipts construct profiles as proof witnesses at
each actual ordinary body entry; no completed body meaning is requested. -/
theorem profile_witnesses : ∀ header, header ∈ headers →
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
      (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) :=
  fun header member => CallableIndexedOwnedNamedPublicProfileExtraction.profiles_for
    compilation functions owner ordinary (outputs header member) catalog

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped outputs syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  classical
  let profiles : ∀ header, header ∈ headers →
      CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
        (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
        (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header :=
    fun header member => @Classical.choice _
      (profile_witnesses functions owner ordinary catalog outputs header member)
  intro scope id lowered
  exact CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds.preserves_at_runtime
    (compilation := compilation) (callerCompilation := callerCompilation)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing (same_layouts publicReceipts) (prefix_matches owner ordinary)
    calleeUninitialized calleeMissing escaped profiles syntaxTrees sameLedger runtimeLedger budget size within

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing ordinary publicReceipts catalog calleeUninitialized calleeMissing escaped outputs syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  classical
  let profiles : ∀ header, header ∈ headers →
      CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
        (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
        (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
        (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header :=
    fun header member => @Classical.choice _
      (profile_witnesses functions owner ordinary catalog outputs header member)
  intro scope id lowered
  exact CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds.reflects_at_runtime
    (compilation := compilation) (callerCompilation := callerCompilation)
    (solved := solved) (reasonAt := reasonAt) (fuel := fuel)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing (same_layouts publicReceipts) (prefix_matches owner ordinary)
    calleeUninitialized calleeMissing escaped profiles syntaxTrees sameLedger runtimeLedger budget size within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadyNamedExpressionBounds
