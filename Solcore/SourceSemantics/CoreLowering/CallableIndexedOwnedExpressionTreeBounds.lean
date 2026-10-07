import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds

/-! The original static expression Tree fold composes actual child states.
Every call receives the real argument post pool and original canonical slots.
The builtin fragment grammar contains no named calls; its proved administrative
leaf effects preserve the complete record observation. Source and Core grades
remain independent, and callee obligations are strictly smaller. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedBoundedContracts
open CallableIndexedOwnedExpressionHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals certificate : GenericExpressionMeaning.Certificate}
  {faults : FunctionCalls.FaultRep}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) {compilation : SourceCoreFunctions.Context}

/-- The supplied original slot proof is paired with the actual input; only the
proof wrapper is forgotten at the actual reached pool. -/
theorem preserves_with_globals {callerPrefix size}
    (meaning : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial globals trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial, globals⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related⟩

/-- Native completion keeps the exact returned pool and its independently
measured source derivation when forgetting the slot proof wrapper. -/
theorem reflects_with_globals {callerPrefix size}
    (meaning : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial globals completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial, globals⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related⟩

include extension faithful functionLeaves functionTypes unique missing in
/-- Compositional heads consume the actual ordered child states. -/
theorem head_preserves_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (callerPrefix budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Stateful.Head.preserves_at functions program evidence
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within unique children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_at functions functionLeaves program evidence unique
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.Stateful.preserves_at functions program evidence
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within unique children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

include extension faithful functionLeaves functionTypes missing in
/-- Reflection uses the same actual child posts at their native grades. -/
theorem head_reflects_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (callerPrefix budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Stateful.Head.reflects_at functions program evidence
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix) budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_at functions functionLeaves program evidence
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.Stateful.reflects_at functions program evidence
      (argumentProtocol (headers := headers) owner callerPrefix) budget size within children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

variable
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
  (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    functions registry header owner.key.frameLocation (conditions header))

include extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- The unchanged static Tree fold closes every expression child. Actual call
bodies remain only at genuine strict Source child grades. -/
theorem preserves_at_with_literals
    (idsUnique : RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) functions evidence
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
    (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (some evidence) headers compilation source context) budget size within
  · intro child childWithin
    exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed _
          (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
            program evidence unique uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    apply head_preserves_at_with_calls functions extension faithful functionLeaves functionTypes evidence unique missing owner
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (some evidence) headers compilation source context) compilation.administrativePrefix budget child childWithin children
    exact PreservesAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
      (CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner sameLayouts conditions authorized
        budget child childWithin idsUnique unique owners
        (fun smaller smallerWithin => preserves_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)

include extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Core children and named hook bodies supply their independent strict grades;
the existing fold returns the separately measured Source trace and real pool. -/
theorem reflects_at_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) functions evidence
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
    (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (some evidence) headers compilation source context) budget size within
  · intro child childWithin
    exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed _
          (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
            program evidence uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    apply head_reflects_at_with_calls functions extension faithful functionLeaves functionTypes evidence missing owner
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (some evidence) headers compilation source context) compilation.administrativePrefix budget child childWithin children
    exact ReflectsAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
      (CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner sameLayouts conditions authorized
        budget child childWithin
        (fun smaller smallerWithin => reflects_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)

include extension faithful functionLeaves functionTypes valid unique owners uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem preserves_at
    (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree
        (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    owner sameLayouts conditions authorized idsUnique
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes valid uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem reflects_at
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree
        (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    owner sameLayouts conditions authorized
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem preserves_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    owner sameLayouts conditions authorized runtime.idsUnique
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults) budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem reflects_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    owner sameLayouts conditions authorized
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults) budget size within bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds
