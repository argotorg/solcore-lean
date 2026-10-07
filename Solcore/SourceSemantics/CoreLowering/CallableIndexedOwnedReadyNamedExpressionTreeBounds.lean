import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads

/-! The original expression support fold consumes strict ready-family named
callee proofs at actual canonical parameter receipts. Arbitrary authentic
callee profiles retain independent Source syntax; no empty-expression body
grammar or completed body law is required by these intermediate adapters. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionTreeBounds
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
  {compilation : SourceCoreFunctions.Context}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- The original canonical caller wraps the same actual ordered pool. -/
abbrev caller := CallableIndexedOwnedAdmittedExpressionTreeBounds.caller (headers := headers)
  (compilation := compilation) owner

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
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

private abbrev calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (some evidence) headers compilation source context

/-- The original full compiler Tree with ordinary literal receipts. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) fuel (.initial compiled.compatible.checked)
    source context solved reasonAt

/-- The same original Tree keeps exact selected runtime numeric receipts. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
    (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
    (reasonAt := reasonAt) (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget child childWithin children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique idsUnique
      sameLayouts escaped profiles owners budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => CallableIndexedOwnedNamedReadyFamilyReceipts.source_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed member (syntaxTrees header member) bodies)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget child childWithin children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique
      sameLayouts escaped profiles budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => CallableIndexedOwnedNamedReadyFamilyReceipts.native_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed member (syntaxTrees header member) bodies)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionTreeBounds
