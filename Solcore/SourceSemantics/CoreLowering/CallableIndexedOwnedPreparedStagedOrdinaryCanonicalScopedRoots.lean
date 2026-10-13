import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport

/-! Each actual ordinary lexical callback keeps its original Source context,
physical scope and retained Code. General expression certificates are recovered
from the real view compiler; finite direct/index authority stays static. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include provenance metadata in
/-- The unchanged compiler action crosses the retained view at the exact
actual child budget and scope, using genuine original body reachability. -/
theorem accepted_original {current : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax function.source id)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation function.source current id code.reasonAt = .ok lowered := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view
  have viewed := syntax_view edited avoids tree reached
  have originalProfile := retained_policy_for_native provenance.policy_recipe metadata current code.reasonAt
  have viewedProfile := retained_policy_on_native provenance.policy_recipe
    (viewed_metadata_native provenance.body_view metadata) current code.reasonAt
  have readView : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      code.policy.readExpression function.source id = code.policy.readExpression code.view id := by
    obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, _same⟩ := provenance.policy_recipe
    exact CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.recipe_read_view recipe edited avoids metadata
  exact CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport.accepted_original_on
    edited avoids (originalProfile.on _) viewedProfile code.callables readView fuel viewed reached accepted

include receiver wellFormed metadata rows complete signatureMember sourceOwner provenance in
/-- The actual binder fields transport typing, ledger and evidence. The root
retains the concrete Code compiler, including its original prefix and reasons. -/
theorem of_child
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, CanonicalRoot compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults headers) := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have originalProfile := retained_policy_for_native provenance.policy_recipe metadata current code.reasonAt
  have profile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      code.policy code.compilation compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source current code.reasonAt := by simpa only [sameSource] using originalProfile
  have coercions : ∀ id actualNode, GeneralSyntax child.source id →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have childTree : GeneralSyntax child.source id := by simpa only [sameSource] using tree
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source current context := by
    simpa only [sameSource] using declarations
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation child.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using accepted_original code support provenance metadata tree reached accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
    compiled.indexed.ancestry.graph.inputs.callable code.active code.callables
    unique childDeclarations profile coercions childTree childFound childTyped compiledChild
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady.calls_ready stagePrepared
      code provenance.policy_recipe metadata support.source_receipt support.unique
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed signatureMember sourceOwner
      selected childTyped certificate childTree
  let root : RootData compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults := {
    compilerFuel := fuel
    accepted := compiledChild
    certificate := certificate
    node := node
    found := childFound
    rawResult := rfl
    typed := childTyped
    sameLedger := fields.solvedRequirements.trans support.body.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    wellFormed := wellFormed
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current readId lowered receipt childReached location
      have originalReached : Reaches function.source [.expression id] (.expression readId) := by
        simpa only [sameSource] using childReached
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support provenance.body_reasons
        receiver (reached.from_root originalReached) (by simpa only [sameSource] using receipt) location
    callsReady := ready }
  exact ⟨⟨node.type, root.canonical rows complete (by rw [support.compilation]; rfl)
    (by rw [support.compilation]; rfl)
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.ordinary_ready support provenance.body_reasons
      sameSource reached certificate)⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedRoots
