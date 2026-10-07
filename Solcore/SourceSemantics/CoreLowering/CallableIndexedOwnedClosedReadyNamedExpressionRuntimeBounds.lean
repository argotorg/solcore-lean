import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedFamilyClosure

/-! The internally closed named family supplies every strict callee body to
the original expression Tree. Runtime leaves retain their authentic ledger;
only original Source and compiler receipts are assumptions of these endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (compilation : CallableIndexedOwnedFunctionValues.Header compiled program → SourceCoreFunctions.Context)
  {callerCompilation : SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- The original canonical caller wraps the same actual ordered pool. -/
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
  (compilation := callerCompilation) owner

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (prefixMatches : ∀ header, header ∈ headers → (compilation header).administrativePrefix = owner.key.capturePrefix + 1)
  (calleeUninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (calleeMissing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.preserves_at_runtime
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
    (compilation := callerCompilation)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing sameLayouts escaped profiles syntaxTrees sameLedger runtimeLedger budget size within
    (fun index child _strict => CallableIndexedOwnedReadyNamedFamilyClosure.preserves_at
      compilation functions owner extension faithful observations functionTypes
      wellFormed owners sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees child index)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (callerCompilation := callerCompilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := callerCompilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionRuntimeBounds.reflects_at_runtime
    (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
    (compilation := callerCompilation)
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing sameLayouts escaped profiles syntaxTrees sameLedger runtimeLedger budget size within
    (fun index child _strict => CallableIndexedOwnedReadyNamedFamilyClosure.reflects_at
      compilation functions owner extension faithful observations functionTypes
      wellFormed sameLayouts prefixMatches calleeUninitialized calleeMissing escaped profiles syntaxTrees child index)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedClosedReadyNamedExpressionRuntimeBounds
