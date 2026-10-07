import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyFamilyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads

/-! The existing expression support fold carries a genuine caller protocol
through ordinary/direct named calls. Its real global-slot carrier and
administrative transport retain additional captured or principal facets at
the same returned pool. Named strict body indices remain authentic. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedReadyFamilyReceipts (body_protocol bridge origin Index)
open CallableIndexedOwnedExpressionHeads (Globals)
universe u

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

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

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

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
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
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
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
        transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget child childWithin children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
      (functions := functions) (owner := owner) (runtime := true) evidence caller wellFormed sourceRuntime covers unique idsUnique
      sameLayouts escaped profiles owners budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => CallableIndexedOwnedNamedReadyFamilyReceipts.source_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed member (syntaxTrees header member) bodies)

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
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
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
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
        transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget child childWithin children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
      (functions := functions) (owner := owner) (runtime := true) evidence caller wellFormed sourceRuntime covers unique
      sameLayouts escaped profiles budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => CallableIndexedOwnedNamedReadyFamilyReceipts.native_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed member (syntaxTrees header member) bodies)

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionCallerBounds.preserves_at_with_literals
    functions extension faithful observations functionTypes owner caller transport evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults)
    budget size within bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol (headers := headers) owner)
          (readiness (bridge (headers := headers) owner)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionCallerBounds.reflects_at_with_literals
    functions extension faithful observations functionTypes owner caller transport evidence wellFormed sourceRuntime covers unique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults)
    budget size within bodies


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionCallerBounds
