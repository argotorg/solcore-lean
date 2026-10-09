import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryFormedMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedRuntimeHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads

/-! The chosen body factory enters the original admitted runtime expression
fold at its genuine nested caller. This bounded Source domain excludes indirect
calls; base-carrier ordinary families and full mixed selection remain separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open RecursiveNamedCatalogInvocationBounds (Below)

/-- A genuine whole-Source sufficient domain, including nested lambda bodies.
It imposes no runtime classification or compiler-output inverse. -/
def NoIndirect (source : TypedSource) : Prop :=
  ∀ {id node callee ids metadata}, source.lookupExpression? id = some node →
    node.form ≠ .call callee ids (.indirect metadata)

/-- Only approved occurrences in the selected body's supported expression
factory are excluded. Other occurrences of the same Source stay unrestricted. -/
def NoIndirectOn (source : TypedSource) (approved : ExpressionId → Prop) : Prop :=
  ∀ {id node callee ids metadata}, approved id → source.lookupExpression? id = some node →
    node.form ≠ .call callee ids (.indirect metadata)

theorem NoIndirect.on {source : TypedSource} (given : NoIndirect source)
    (approved : ExpressionId → Prop) : NoIndirectOn source approved := by
  intro id node callee ids metadata _allowed found
  exact given found

/-- Internal domain paired with the actual static certificate mode. -/
def DomainFor (supported : Bool) (source : TypedSource) (approved : ExpressionId → Prop) : Prop :=
  if supported then NoIndirectOn source approved else NoIndirect source

namespace Shared

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (supported : Bool)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (certificates root expressionSyntax))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
  (covers : evidence.Covers sourceContext) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique sourceContext)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : DomainFor supported (source caller.named) (expressionSyntax (source caller.named)))

theorem head_filter {children childScope id lowered}
    (given : DomainFor supported (source caller.named) (expressionSyntax (source caller.named)))
    (certified : CallsFor root expressionSyntax factory headers supported children childScope id lowered) :
    BodyCalls root expressionSyntax factory headers children childScope id lowered ∧
      AbsentAt (source caller.named) id := by
  cases supported
  · exact ⟨certified, fun found => given found⟩
  · obtain ⟨actual, allowed | absent⟩ := certified
    · exact ⟨actual, fun found => given allowed found⟩
    · exact ⟨actual, absent⟩

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem head_preserve {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (CallsFor root expressionSyntax factory headers supported children) faults size := by
  intro requestedScope id lowered certified
  obtain ⟨actualHead, excluded⟩ := head_filter root expressionSyntax supported factory noIndirect certified
  cases actualHead with
  | named actual =>
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.preserves_head
      (compilation := context compiled.indexed caller.named) (certificate := children)
      functions owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
      evidence wellFormed runtime covers unique owners idsUnique sameLayouts
      budget size headWithin arguments
      (fun header member => CallableIndexedOwnedPreparedMixedRuntimeHeads.named_source_bodies
        functions owner outer budget within ih header member) actual
  | prepared_lambda found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate chosen metadata =>
    exact CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.preserves_head_at
      caller sourceContext evidence root expressionSyntax owner profile functions members
      complete globals slots prefixZero wellFormed runtime covers rfl size (.formed receipt chosen)
  | prepared_indirect found form receipt ordered =>
    exact False.elim (excluded found form)

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem head_reflect {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (CallsFor root expressionSyntax factory headers supported children) faults size := by
  intro requestedScope id lowered certified
  obtain ⟨actualHead, excluded⟩ := head_filter root expressionSyntax supported factory noIndirect certified
  cases actualHead with
  | named actual =>
    exact CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds.reflects_head
      (compilation := context compiled.indexed caller.named) (certificate := children)
      functions owner (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
      evidence wellFormed runtime covers unique sameLayouts
      budget size headWithin arguments
      (fun header member => CallableIndexedOwnedPreparedMixedRuntimeHeads.named_native_bodies
        functions owner outer budget within ih header member) actual
  | prepared_lambda found form certificate receipt samePolicy sameBody sameFuel sameView sameReason sameCertificate chosen metadata =>
    exact CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.reflects_head_at
      caller sourceContext evidence root expressionSyntax owner profile functions members
      complete globals slots prefixZero wellFormed runtime covers rfl size (.formed receipt chosen)
  | prepared_indirect found form receipt ordered =>
    exact False.elim (excluded found form)

section Trees
variable {fuel : Nat} {solved : List SolvedRequirement}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem tree_preserve
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (CallsFor root expressionSyntax factory headers supported) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size := by
  let transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (CallsFor root expressionSyntax factory headers supported) budget size headWithin
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              (Program.ofChecked compiled.sourceProgram) evidence unique uninitialized missing
              (CompatibleExpressionLiteralRuntime.preserves functions (Program.ofChecked compiled.sourceProgram)
                sourceContext evidence valid.ledger valid.runtime unique faults))) child))
  · intro childCertificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (CallsFor root expressionSyntax factory headers supported) budget child childWithin children
    exact head_preserve root expressionSyntax supported functions members factory profile owner wellFormed runtime covers unique sameLayouts
      owners idsUnique complete globals slots prefixZero noIndirect outer budget child childWithin within
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) ih

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem tree_reflect
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (CallsFor root expressionSyntax factory headers supported) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size := by
  let transport := CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (CallsFor root expressionSyntax factory headers supported) budget size headWithin
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              (Program.ofChecked compiled.sourceProgram) evidence uninitialized missing
              (CompatibleExpressionLiteralRuntime.reflects functions (Program.ofChecked compiled.sourceProgram)
                sourceContext evidence valid.ledger valid.runtime (source caller.named) faults))) child))
  · intro childCertificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (CallsFor root expressionSyntax factory headers supported) budget child childWithin children
    exact head_reflect root expressionSyntax supported functions members factory profile owner wellFormed runtime covers unique sameLayouts
      complete globals slots prefixZero noIndirect outer budget child childWithin within
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) ih

end Trees

section Support
variable {formationContext : SourceSemantics.Context} {formationEvidence : Dynamic.EvidenceEnvironment}
  {formationScope : SourceCoreLocalCell.Scope} {formationId : ExpressionId} {formationCode : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    formationContext formationEvidence formationScope formationId formationCode)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  (domains : ∀ childScope, DomainAt root expressionSyntax receipt.formation.body.readFuel sourceContext formationEvidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements
    sourceContext formationEvidence)

include profile members chosen domains valid wellFormed sameLayouts owners complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem support_preserve
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (actualIds : RequirementIdsUnique sourceContext) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size := by
  intro childScope child output actual node found typed mapping world administrativeContext sourceEnvironment
    canonical actualEnvironment actualContext before store ξ result after environmentRep heaps agrees renamed
    runtimeTypes initial admitted evaluation
  let domain := domains childScope
  have tree := support_cover_for root expressionSyntax receipt supported chosen environment headers domain valid actualRuntime actual
  exact tree_preserve root expressionSyntax supported functions members
    (indirect_factory root expressionSyntax headers domain valid) profile owner wellFormed actualRuntime valid.covers
    (actualRuntime.graph.nodeOccurrencesUnique) sameLayouts owners actualIds complete globals slots prefixZero noIndirect
    extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih tree found typed environmentRep heaps agrees renamed runtimeTypes initial admitted evaluation

include profile members chosen domains valid wellFormed sameLayouts complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem support_reflect
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size := by
  intro childScope child output actual node found typed mapping world administrativeContext sourceEnvironment
    canonical actualEnvironment actualContext before store ξ result after environmentRep heaps agrees renamed
    runtimeTypes initial admitted evaluation
  let domain := domains childScope
  have tree := support_cover_for root expressionSyntax receipt supported chosen environment headers domain valid actualRuntime actual
  exact tree_reflect root expressionSyntax supported functions members
    (indirect_factory root expressionSyntax headers domain valid) profile owner wellFormed actualRuntime valid.covers
    (actualRuntime.graph.nodeOccurrencesUnique) sameLayouts complete globals slots prefixZero noIndirect
    extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih tree found typed environmentRep heaps agrees renamed runtimeTypes initial admitted evaluation

end Support
end Shared

namespace ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (certificates root expressionSyntax))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
  (covers : evidence.Covers sourceContext) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique sourceContext)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : NoIndirect (source caller.named))

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem preserves_calls {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (BodyCalls root expressionSyntax factory headers children) faults size :=
  Shared.head_preserve root expressionSyntax false functions members
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem reflects_calls {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (BodyCalls root expressionSyntax factory headers children) faults size :=
  Shared.head_reflect root expressionSyntax false functions members
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

section Trees
variable {fuel : Nat} {solved : List SolvedRequirement}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem preserves_tree_at_runtime
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (BodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  Shared.tree_preserve root expressionSyntax false functions members
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem reflects_tree_at_runtime
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (BodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  Shared.tree_reflect root expressionSyntax false functions members
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

end Trees

section Support
variable {formationContext : SourceSemantics.Context} {formationEvidence : Dynamic.EvidenceEnvironment}
  {formationScope : SourceCoreLocalCell.Scope} {formationId : ExpressionId} {formationCode : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    formationContext formationEvidence formationScope formationId formationCode)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  (domains : ∀ childScope, DomainAt root expressionSyntax receipt.formation.body.readFuel sourceContext formationEvidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements
    sourceContext formationEvidence)

include profile members chosen domains valid wellFormed sameLayouts owners complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem preserves_at_support
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (actualIds : RequirementIdsUnique sourceContext) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  Shared.support_preserve root expressionSyntax false functions members
    profile owner wellFormed sameLayouts owners complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih actualIds

include profile members chosen domains valid wellFormed sameLayouts complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem reflects_at_support
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  Shared.support_reflect root expressionSyntax false functions members
    profile owner wellFormed sameLayouts complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih

end Support
end ForModel

namespace ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (certificates root expressionSyntax))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
  (covers : evidence.Covers sourceContext) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique sourceContext)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : NoIndirectOn (source caller.named) (expressionSyntax (source caller.named)))

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem preserves_calls_on {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (ScopedBodyCalls root expressionSyntax factory headers children) faults size :=
  Shared.head_preserve root expressionSyntax true functions members
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem reflects_calls_on {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (ScopedBodyCalls root expressionSyntax factory headers children) faults size :=
  Shared.head_reflect root expressionSyntax true functions members
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

section Trees
variable {fuel : Nat} {solved : List SolvedRequirement}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))

include profile members wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem preserves_tree_on
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (ScopedBodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  Shared.tree_preserve root expressionSyntax true functions members
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

include profile members wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem reflects_tree_on
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (ScopedBodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  Shared.tree_reflect root expressionSyntax true functions members
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

end Trees

section Support
variable {formationContext : SourceSemantics.Context} {formationEvidence : Dynamic.EvidenceEnvironment}
  {formationScope : SourceCoreLocalCell.Scope} {formationId : ExpressionId} {formationCode : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    formationContext formationEvidence formationScope formationId formationCode)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  (domains : ∀ childScope, DomainAt root expressionSyntax receipt.formation.body.readFuel sourceContext formationEvidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements
    sourceContext formationEvidence)

include profile members chosen domains valid wellFormed sameLayouts owners complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem preserves_support_on
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (actualIds : RequirementIdsUnique sourceContext) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  Shared.support_preserve root expressionSyntax true functions members
    profile owner wellFormed sameLayouts owners complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih actualIds

include profile members chosen domains valid wellFormed sameLayouts complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem reflects_support_on
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  Shared.support_reflect root expressionSyntax true functions members
    profile owner wellFormed sameLayouts complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih

end Support
end ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (certificates root expressionSyntax))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
  (covers : evidence.Covers sourceContext) (unique : NodeOccurrencesUnique (source caller.named))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique sourceContext)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : NoIndirect (source caller.named))

include wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem preserves_calls {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext evidence (source caller.named)
      (BodyCalls root expressionSyntax factory headers children) faults size :=
  ForModel.preserves_calls root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

include wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect in
/-- Finite actual named and lambda leaves supply the same admitted tuple.
Indirect is excluded only by its true Source lookup and form. -/
theorem reflects_calls {children : GenericExpressionMeaning.Certificate}
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) sourceContext evidence (source caller.named) children faults))
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext evidence (source caller.named)
      (BodyCalls root expressionSyntax factory headers children) faults size :=
  ForModel.reflects_calls root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect outer budget size headWithin within arguments ih

section Trees
variable {fuel : Nat} {solved : List SolvedRequirement}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))

include wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem preserves_tree_at_runtime
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (BodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  ForModel.preserves_tree_at_runtime root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    factory profile owner wellFormed runtime covers unique sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

include wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing in
/-- The original admitted support fold consumes the finite BodyCalls producer.
Runtime literal evidence is derived from the complete actual ledger. -/
theorem reflects_tree_at_runtime
    (valid : CompatibleRuntimeContextValidity.Valid solved sourceContext evidence)
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext evidence (source caller.named)
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
        (BodyCalls root expressionSyntax factory headers) fuel (.initial compiled.compatible.checked)
        (source caller.named) sourceContext solved rootReasonAt) faults size :=
  ForModel.reflects_tree_at_runtime root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    factory profile owner wellFormed runtime covers unique sameLayouts complete globals slots prefixZero noIndirect extension faithful observations functionTypes uninitialized missing valid outer budget size headWithin within ih

end Trees

section Support
variable {formationContext : SourceSemantics.Context} {formationEvidence : Dynamic.EvidenceEnvironment}
  {formationScope : SourceCoreLocalCell.Scope} {formationId : ExpressionId} {formationCode : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    formationContext formationEvidence formationScope formationId formationCode)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  (domains : ∀ childScope, DomainAt root expressionSyntax receipt.formation.body.readFuel sourceContext formationEvidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed caller.named).solvedRequirements
    sourceContext formationEvidence)

include chosen domains valid wellFormed sameLayouts owners complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem preserves_at_support
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
    (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i))
    (actualIds : RequirementIdsUnique sourceContext) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  ForModel.preserves_at_support root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    profile owner wellFormed sameLayouts owners complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih actualIds

include chosen domains valid wellFormed sameLayouts complete globals slots prefixZero noIndirect in
/-- The actual certificate comes from the same recaptured Support. Its Tree
is constructed internally from the genuine chosen factory and accepted action. -/
theorem reflects_at_support
    (actualRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
    (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
    (outer budget size : Nat) (headWithin : size ≤ budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      sourceContext formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source sourceContext) faults size :=
  ForModel.reflects_at_support root expressionSyntax
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    (fun _i _history member => member.formed.represents)
    profile owner wellFormed sameLayouts complete globals slots prefixZero noIndirect receipt chosen environment domains valid actualRuntime extension faithful observations functionTypes uninitialized missing outer budget size headWithin within ih

end Support
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyRuntimeBounds
