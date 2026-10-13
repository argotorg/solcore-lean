import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryTerminalChoice
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics

/-! Actual ordinary closure formation supplies canonical terminal roots at
its original Source and parameter context. The finite inventory supplies direct
callee authority; actual capture slots are supplied later by parameter entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
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

private abbrev parameterScope {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include provenance metadata in
/-- The original compiler's full contextual action crosses its retained body
view at the same clipped child budget. Synthetic callees are validated statically. -/
theorem accepted_original
    (packet : Terminal code stages)
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt)
    (tree : GeneralSyntax function.source packet.expression) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody
      (min packet.receipt.childFuel code.fuel) code.compilation function.source
      (parameterScope code) packet.expression code.reasonAt = .ok packet.receipt.child := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view
  have reached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
  have viewed := syntax_view edited avoids tree reached
  have originalProfile := retained_policy_for_native provenance.policy_recipe metadata (parameterScope code) code.reasonAt
  have viewedProfile := retained_policy_on_native provenance.policy_recipe
    (viewed_metadata_native provenance.body_view metadata) (parameterScope code) code.reasonAt
  have readView : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      code.policy.readExpression function.source id = code.policy.readExpression code.view id := by
    obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, _same⟩ := provenance.policy_recipe
    exact CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.recipe_read_view recipe edited avoids metadata
  exact CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport.accepted_original_on
    edited avoids (originalProfile.on _) viewedProfile code.callables readView
    (min packet.receipt.childFuel code.fuel) viewed reached
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason)

include receiver wellFormed metadata rows complete signatureMember sourceOwner provenance in
/-- Every selected invocation receives a certificate from the actual original
compiler action and original Source frame. No body execution is a premise. -/
def at_scope
    (packet : Terminal code stages)
    (callback : packet.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (reason : packet.reasonAt = code.reasonAt)
    (tree : GeneralSyntax function.source packet.expression)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    CanonicalRoot compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      support.body.toContext.context child code.reasonAt (parameterScope code)
      packet.expression packet.receipt.child function.resultType faults headers := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selected
  have originalProfile := retained_policy_for_native provenance.policy_recipe metadata (parameterScope code) code.reasonAt
  have profile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
      code.policy code.compilation compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source (parameterScope code) code.reasonAt := by simpa only [sameSource] using originalProfile
  have coercions : ∀ id node, GeneralSyntax child.source id → child.source.lookupExpression? id = some node →
      node.coercions = [] := by
    intro id node syntaxTree found
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree) node
      (by simpa only [sameSource] using found)
  have syntaxTree : GeneralSyntax child.source packet.expression := by simpa only [sameSource] using tree
  have available : (child.source.lookupExpression? packet.expression).isSome := by
    obtain ⟨node, found⟩ := syntax_found syntaxTree
    exact Option.isSome_of_eq_some found
  let node := (child.source.lookupExpression? packet.expression).get available
  have found : child.source.lookupExpression? packet.expression = some node := Option.eq_some_of_isSome available
  have properties : node.type = function.resultType ∧
      ExpressionHasType child.source support.body.toContext.context packet.expression node.type := by
    obtain ⟨actual, selectedNode, rawType, typed⟩ :=
      CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
        code packet support.body.toContext support.body.frame child selected
    exact (Option.some.inj (selectedNode.symm.trans found)) ▸ ⟨rawType, typed⟩
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody
      (min packet.receipt.childFuel code.fuel) code.compilation child.source (parameterScope code)
      packet.expression code.reasonAt = .ok packet.receipt.child := by
    simpa only [sameSource] using accepted_original stagePrepared code support provenance metadata packet callback reason tree
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
    compiled.indexed.ancestry.graph.inputs.callable code.active code.callables
    unique declarations profile coercions syntaxTree found properties.2 accepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady.calls_ready stagePrepared
      code provenance.policy_recipe metadata support.source_receipt support.unique (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      wellFormed signatureMember sourceOwner selected properties.2 certificate syntaxTree
  let root : RootData compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      support.body.toContext.context child code.reasonAt (parameterScope code)
      packet.expression packet.receipt.child function.resultType faults := {
    compilerFuel := min packet.receipt.childFuel code.fuel
    accepted := accepted
    certificate := certificate
    node := node
    found := found
    rawResult := properties.1
    typed := properties.2
    sameLedger := support.body.valid.ledger
    runtimeLedger := support.body.valid.runtime
    unique := unique
    wellFormed := wellFormed
    runtime := by
      rw [sameSource]
      exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1
    covers := by rw [(stages).evidence selected]; exact support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current id lowered receipt reached location
      have rootReached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
      have originalReached : Reaches function.source [.expression packet.expression] (.expression id) := by
        simpa only [sameSource] using reached
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support provenance.body_reasons
        receiver (rootReached.from_root originalReached) (by simpa only [sameSource] using receipt) location
    callsReady := ready }
  exact root.canonical rows complete (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
    (fun compiler path => by
      have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path syntaxTree
      refine ⟨(actualTree.direct_site compiler.metadata.found compiler.form).ordinary code.compilation.plan, ?_⟩
      have requirements := metadata.requirements _ (by simpa only [sameSource] using actualTree)
        compiler.node (by simpa only [sameSource] using compiler.metadata.found)
      rcases requirements with empty | ⟨literal, resolution, form⟩
      · exact empty
      · rw [compiler.form] at form
        cases form)
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.ordinary_ready support provenance.body_reasons
      sameSource (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet) certificate)

include receiver wellFormed metadata rows complete signatureMember sourceOwner provenance in
/-- The accepted ordinary factory and complete Header inventory issue the
terminal packet and every selected canonical root. Runtime captures remain
those of the actual recaptured Code. -/
theorem of_actual
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (tree : GeneralSyntax function.source expression)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedCanonicalBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  exact at_scope stagePrepared code support provenance receiver wellFormed metadata rows complete
    signatureMember sourceOwner packet callback reason (expressionEq.symm ▸ tree) selectedChild selectedAt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
