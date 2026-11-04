import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-!
# Owned callables: ready expressions

Tree, runtime and caller bounds of ready named expressions, and the family closure.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionTreeBounds
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionRuntimeBounds
/-! Runtime literal leaves come from the original requirement ledger.
These finite wrappers supply their already proved meanings internally while
retaining the same canonical named family children and actual caller state. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionRuntimeBounds
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
private abbrev caller := CallableIndexedOwnedReadyNamedExpressionTreeBounds.caller (headers := headers)
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

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
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
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionTreeBounds.preserves_at_with_literals
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults)
    budget size within bodies

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
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
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNamedExpressionTreeBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNamedExpressionTreeBounds.reflects_at_with_literals
    functions extension faithful observations functionTypes owner evidence wellFormed sourceRuntime covers unique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults)
    budget size within bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedFamilyClosure
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
    (origin compilation) functions program
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
    (origin compilation) functions program
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds
/-! Genuine named parameter entries retain their original principal packet
when supplying strict body children. The unchanged expression support fold
carries the actual caller through named calls; nested formation authority is
never reconstructed from bare global slots. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedNamedNestedReadyFamilyReceipts (body_protocol bridge origin Index)
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
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
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

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol true index)
          (readiness (bridge true index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
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
      (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member) member (syntaxTrees header member) bodies)

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol true index)
          (readiness (bridge true index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
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
      (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
        (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member) member (syntaxTrees header member) bodies)

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (body_protocol true index)
          (readiness (bridge true index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.preserves_at_with_literals
    functions extension faithful observations functionTypes owner prefixZero globalCounts caller transport evidence wellFormed sourceRuntime covers unique owners idsUnique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults)
    budget size within bodies

include prefixZero globalCounts transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles syntaxTrees in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ index : Index (headers := headers) (keys := keys) (certificates := certificates)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable)
      (registry := registry) (faults := faults) true,
      RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (body_protocol true index)
          (readiness (bridge true index)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
          (ProtectedStateImperativeTypedSourceSites.Facts (origin true index).function.source (origin true index).expressionSyntax)
          functions program (origin true index))) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.RuntimeTree (headers := headers)
        (compilation := compilation) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  exact CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds.reflects_at_with_literals
    functions extension faithful observations functionTypes owner prefixZero globalCounts caller transport evidence wellFormed sourceRuntime covers unique
    uninitialized missing sameLayouts escaped profiles syntaxTrees
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults)
    budget size within bodies


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNestedNamedExpressionCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionCallerBounds
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionHeads
/-! Genuine ordinary and direct named heads consume the shared family's strict
callee meanings at the actual parameter receipt. The original head and caller
protocol are retained, with independent Source and native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission ProtectedStateTransition
open CallableIndexedOwnedAdmittedNamedExpressionHeads
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {ι : Type}
  (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  (wellFormed : ProgramWellFormed program)

/-- Static associations cover each genuine parameter receipt. They retain its
whole compiler origin and independent body Syntax, with no execution premise. -/
def AssociationsFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Type :=
  ∀ {initial : Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
    ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) argumentsPool header arguments,
    CallableIndexedOwnedNamedReadyContinuations.Association functions owner runtime origins receipt wellFormed

private abbrev bodyBridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) header)
  (associations : ∀ header, header ∈ headers → AssociationsFor (headers := headers) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) functions owner runtime origins wellFormed header)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)

include wellFormed sourceRuntime covers unique idsUnique sameLayouts escaped profiles associations owners in
/-- Named Source heads use only their strict child expressions and the same
shared family's strict associated body contracts. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
    (functions := functions) (owner := owner) (runtime := runtime) evidence bridge wellFormed sourceRuntime covers unique idsUnique
    sameLayouts escaped profiles owners budget size within children
    (fun header member => CallableIndexedOwnedNamedReadyContinuations.source_bodies
      (functions := functions) (owner := owner) (runtime := runtime) (origins := origins)
      wellFormed (associations header member) bodies)

include wellFormed sourceRuntime covers unique sameLayouts escaped profiles associations in
/-- Native head inversion uses the strict native body bound. Its Source result
has an independent grade and the same actual reached parameter pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
    (functions := functions) (owner := owner) (runtime := runtime) evidence bridge wellFormed sourceRuntime covers unique
    sameLayouts escaped profiles budget size within children
    (fun header member => CallableIndexedOwnedNamedReadyContinuations.native_bodies
      (functions := functions) (owner := owner) (runtime := runtime) (origins := origins)
      wellFormed (associations header member) bodies)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionHeads
end
