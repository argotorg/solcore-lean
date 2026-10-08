import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime

/-! Genuine named parameter receipts enter the original low call cores. The
same expression support fold supplies ordered strict children and runtime
literal leaves while retaining the caller's complete actual pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

section Heads
variable {certificate : GenericExpressionMeaning.Certificate}

include wellFormed sourceRuntime covers unique idsUnique sameLayouts owners in
/-- The authentic Source row selects actual ordered arguments and their real
parameter receipt before the strict body child is consumed. -/
theorem preserves_head (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedPreparedNamedParameterReceipts.source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application budget (bodies header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

include wellFormed sourceRuntime covers unique sameLayouts in
/-- Native arguments recover their independent Source trace at the actual
post before the genuine parameter and body continuations are selected. -/
theorem reflects_head (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedPreparedNamedParameterReceipts.native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application budget (bodies header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

end Heads

section Trees
variable {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

private abbrev calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (some evidence) headers compilation source context

/-- The original compiler Tree keeps its genuine named call certificates. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (calls (headers := headers) (compilation := compilation)
    (source := source) (context := context) evidence) fuel (.initial compiled.compatible.checked) source context solved reasonAt

/-- Runtime literal certificates remain the original selected ledger leaves. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
    (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed sourceRuntime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
      budget child childWithin children
    exact preserves_head functions owner caller evidence wellFormed sourceRuntime covers unique owners idsUnique sameLayouts
      budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed sourceRuntime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
      budget child childWithin children
    exact reflects_head functions owner caller evidence wellFormed sourceRuntime covers unique sameLayouts
      budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  preserves_at_with_literals functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique owners idsUnique sameLayouts uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults)
    budget size within bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  reflects_at_with_literals functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique sameLayouts uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults)
    budget size within bodies

end Trees
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
