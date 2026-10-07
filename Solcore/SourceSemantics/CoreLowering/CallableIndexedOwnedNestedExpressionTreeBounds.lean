import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads

/-! The same static expression Tree fold carries the actual nested formation
packet through every compositional child. Genuine original View calls consume
ordered actual argument states; literal lambdas use full reached owner receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedBoundedContracts
open CallableIndexedLambdaNestedRuntimeBodyMeaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  {rank : Nat}
variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header)
  (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header owner.key.frameLocation (conditions header))

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- The unchanged static Tree fold closes every expression child. Actual call
bodies remain only at genuine strict Source child grades. -/
theorem preserves_at_with_literals
    (idsUnique : RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  refine RecursiveNamedExpressionTreeBounds.preserves_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) evidence
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence)) budget size within ?_ ?_
  · intro child childWithin
    exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed _
          (CompatibleExpressionBuiltins.preserves_with_literals (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes
            program evidence unique uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    exact ProtectedStateExpressionCallsHeads.head_preserves_at_with_calls (certificate := childCertificate)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes evidence unique missing
      (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence) (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      budget child childWithin children
      (CallableIndexedOwnedNestedExpressionHeads.nested_preserves_at_with (certificate := childCertificate)
        owner caller prefixZero profile complete globals slots sameSource
        sameLayouts conditions authorized budget child childWithin idsUnique unique owners
        (fun smaller smallerWithin => children smaller (Nat.le_of_lt smallerWithin)) bodies)

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Core children and named hook bodies supply their independent strict grades;
the existing fold returns the separately measured Source trace and real pool. -/
theorem reflects_at_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  refine RecursiveNamedExpressionTreeBounds.reflects_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) evidence
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence)) budget size within ?_ ?_
  · intro child childWithin
    exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed _
          (CompatibleExpressionBuiltins.reflects_with_literals (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes
            program evidence uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    exact ProtectedStateExpressionCallsHeads.head_reflects_at_with_calls (certificate := childCertificate)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension faithful functionLeaves functionTypes evidence missing
      (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence) (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller)
      budget child childWithin children
      (CallableIndexedOwnedNestedExpressionHeads.nested_reflects_at_with (certificate := childCertificate)
        owner caller prefixZero profile complete globals slots sameSource
        sameLayouts conditions authorized budget child childWithin
        (fun smaller smallerWithin => children smaller (Nat.le_of_lt smallerWithin)) bodies)

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes valid unique owners uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem preserves_at
    (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree
        ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact preserves_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    sameLayouts conditions authorized idsUnique
    (CompatibleExpressionLiterals.preserves (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes valid uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem reflects_at
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree
        ((CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact reflects_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence uninitialized missing
    sameLayouts conditions authorized
    (CompatibleExpressionLiterals.reflects (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
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
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  preserves_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    sameLayouts conditions authorized runtime.idsUnique
    (CompatibleExpressionLiteralRuntime.preserves (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence sameLedger runtime unique faults) budget size within bodies

include prefixZero complete globals slots sameSource extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
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
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := (CallableIndexedLambdaNestedRuntimeCertificates.Head (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
          (LowerSupport (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers caller registry faults rank)
          rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence))
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  reflects_at_with_literals owner caller prefixZero profile complete globals slots sameSource extension faithful functionLeaves functionTypes evidence uninitialized missing
    sameLayouts conditions authorized
    (CompatibleExpressionLiteralRuntime.reflects (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program context evidence sameLedger runtime source faults) budget size within bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
