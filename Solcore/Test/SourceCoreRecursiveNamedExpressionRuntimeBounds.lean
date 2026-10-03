import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.Test.SourceCoreRecursiveNamedExpressionBounds

/-! Actual named compiler success returns support for the same complete Tree.
Final bounded consumers use the whole runtime ledger, without caller ordinary
validity or an expression runtime premise. Callee BodyBelow and static source,
policy, coverage and constructor conditions remain explicit at this boundary.
The singleton-body consumers also close BodyBelow from a concrete old body.
Header/Profile/Covers are unchanged. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedExpressionRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_contextual_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_at_runtime

section ActualCompilation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {locations : Locations} {capturePrefix : Nat}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include extension faithful functionLeaves functionTypes in
theorem actual_functions_preserves_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners uninitialized missing sameLedger runtime budget size within bodies receipt rootFound


include extension faithful functionLeaves functionTypes in
theorem actual_functions_reflects_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence uninitialized missing sameLedger runtime budget size within bodies receipt rootFound

end ActualCompilation

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))



include extension uninitialized missing faithful functionLeaves functionTypes sameLedger runtime unique owners callerUninitialized callerMissing in
/-- Every child is supplied by the same recursive Tree; the concrete body
certificate closes the actual remaining body family. -/
theorem concrete_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RuntimeExpressions [Header.of_body body] compilation readFuel source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners callerUninitialized callerMissing sameLedger runtime budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_preserves_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes sameLedger runtime callerUninitialized callerMissing in
/-- Completed Core code produces an independent source trace; the body is
proved from its finite static certificate rather than supplied as execution. -/
theorem concrete_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RuntimeExpressions [Header.of_body body] compilation readFuel source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence callerUninitialized callerMissing sameLedger runtime budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_reflects_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

section Boundaries
/-- Support is attached to the same child proof and emitted code. -/
theorem same_tree {calls : CompatibleExpressionCalls.CallHeads} {fuel : Nat} {values : RecursiveNamedCatalog.ValuesContext}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := values)
      (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) scope id code) :
    CompatibleExpressionCalls.Tree calls fuel values source context solved reasonAt scope id code := receipt.choose

/-- Full ledger equality retains every unused row at this exact context. -/
theorem unused_row {solved : List SolvedRequirement} {context : SourceSemantics.Context}
    (sameLedger : context.solvedRequirements = solved) {row : SolvedRequirement} (unused : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [sameLedger]; exact unused

end Boundaries
end Tests.SourceCoreRecursiveNamedExpressionRuntimeBounds
