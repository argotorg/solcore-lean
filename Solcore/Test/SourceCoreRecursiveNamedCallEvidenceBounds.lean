import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.Test.SourceCoreRecursiveNamedPreparedCallEvidence
import Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning

/-! Actual accepted named expressions keep one caller dictionary through all
ordered children. The catalog closes callee BodyBelow internally with the same
static profile family; reflection takes no source trace or preservation law.
Ordinary source flags, coercion-free admission, all ranges, source typing,
full ledger validity, diagnostic interpretation and entry authority remain
independent conditions. The runtime fixture reuses the real nonempty dictionary
compiler audit, including duplicate predicates and original argument order. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedCallEvidenceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_prepared_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_prepared
abbrev actual_header := @RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
abbrev actual_extraction := @RecursiveNamedCatalogRuntimeProfileFactory.extract_source_with

section ActualCompilation

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {callerCompilation : SourceCoreFunctions.Context} (evidence : Dynamic.EvidenceEnvironment)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
theorem actual_preserves_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers callerCompilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptySelected : SelectedEmptyEvidence headers callerCompilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered callerCompilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers callerCompilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) (some evidence) policy callerCompilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel callerCompilation source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid callerCompilation.solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_evidence (some evidence)
    admission coverage sourceTypes emptySelected order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_preserves_at_runtime_evidence functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid unique callerUninitialized callerMissing size receipt rootFound


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
theorem actual_reflects_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers callerCompilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptySelected : SelectedEmptyEvidence headers callerCompilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered callerCompilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers callerCompilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) (some evidence) policy callerCompilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel callerCompilation source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid callerCompilation.solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_evidence (some evidence)
    admission coverage sourceTypes emptySelected order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_reflects_at_runtime_evidence functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size receipt rootFound

end ActualCompilation

section Boundaries
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {code : SourceCoreBasic.LoweredExpr}

theorem same_tree
    (receipt : RuntimeExpressionsWith (some evidence) headers compilation readFuel source context solved reasonAt scope id code) :
    CompatibleExpressionCalls.Tree
      (RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence)
      readFuel values source context solved reasonAt scope id code := receipt.choose

theorem unused_rows_kept (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) :
    context.solvedRequirements = solved := valid.ledger

theorem dictionary_keeps_duplicates (first second : TypedTraitResolution.Evidence) :
    CallableNamedMetadata.environment [first, second, first] =
      [(SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first),
       (SourceTypedRuntime.runtimeEvidenceGoal second, CallableNamedMetadata.evidence second),
       (SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first)] := rfl

theorem empty_family_unchanged :
    RecursiveNamedCallEvidenceHeads.Calls none headers compilation source context =
      RecursiveNamedCatalog.Head headers compilation source context := rfl

theorem duplicate_requirement_ids_rejected (row : SolvedRequirement) :
    ¬ RequirementIdsUnique {context with solvedRequirements := [row, row]} := by
  simp [RequirementIdsUnique]

end Boundaries

def run : IO Unit := do
  SourceCoreRecursiveNamedPreparedCallEvidence.run
  SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning.run

end Tests.SourceCoreRecursiveNamedCallEvidenceBounds
