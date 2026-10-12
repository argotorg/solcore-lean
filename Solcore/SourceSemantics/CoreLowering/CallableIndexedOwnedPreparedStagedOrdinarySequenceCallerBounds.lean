import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning

/-! Connect actual ordinary-owner sequence receipts to the existing numeric
caller/body proof. Ordinary Associations keep their exact Code and BodyWith
context; their sequence packets and child call readiness are derived from
preparation. Principal and named body support remain explicit static inputs.
Full retained policy, original metadata and sequence conditions are retained.

The combined named/anonymous registry is used throughout. The actual ordinary
caller's exact call ports and ordinary sequence coverage are constructed here.
No expression execution or whole-body meaning law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
  (Choice Conditions ChoiceFor ConditionsFor ReadyFor ShapeFor choose_for packet_for support_for)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Syntax)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableAncestryMetadata (eraseRequirements)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)


private theorem sidecar_member {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreStageContracts.prepareSidecar plan owner = .ok sidecar) :
    sidecar.caller ∈ plan.specializations := by
  have found := LambdaSourceAlignment.sidecar_lookup issued
  have filtered := CallableIndexedOwnedContextualDiagnosticSources.selected_filter found
  have member : sidecar.caller ∈ plan.specializations.filter
      (fun row => decide (row.key = owner)) := by
    rw [filtered]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp member).1

/-- The combined registry also has a named selection. Its literal prepared
source supplies the same erasure boundary; an anonymous selection keeps the
existing authenticated ancestry proof. -/
private theorem selected_canonical {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    ∃ sidecar active,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan sidecar.caller.key = .ok sidecar ∧
      invocation = RecursiveStageRegistry.scope sidecar active function ∧
      eraseRequirements function.source =
        eraseRequirements (sidecar.source.applySubstitution active) := by
  cases selected with
  | anonymous receipt =>
      exact CallableSelectedCanonicalSourceErasure.selected_canonical receipt
  | named prepared sidecar issued same =>
      have sourceEq : prepared.view.source = sidecar.source := by
        change prepared.named.specialized.function.typedBody = sidecar.caller.function.typedBody
        rw [prepared.same, same]
      exact ⟨sidecar, [], by simpa only [same] using issued, rfl,
        by simpa using congrArg eraseRequirements sourceEq⟩

private theorem selected_frame {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    {canonical : SourceCoreStageContracts.Sidecar} {owner : SourceCompilationPlan.Key}
    {active : TypeSystem.Substitution} {signature : ProgramFunctionSignature}
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan owner = .ok canonical)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      owner active function.source)
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    invocation.guards = CallableLedger.frame canonical := by
  obtain ⟨sidecar, selectedActive, issued, scopeEq, erased⟩ :=
    selected_canonical stagePrepared selected
  have canonicalSourceEq := canonicalSource.source canonicalIssued
  have selectedOwner : sidecar.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner erased
    change function.source.owner = sidecar.caller.function.typedBody.owner at same
    exact same.symm.trans sourceOwner
  have canonicalOwner : canonical.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner canonicalSourceEq
    exact same.symm.trans sourceOwner
  have selectedOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted wellFormed.signatures signatureMember _ (sidecar_member issued) selectedOwner
  have canonicalOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted wellFormed.signatures signatureMember _ (sidecar_member canonicalIssued) canonicalOwner
  have samePlan : sidecar.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted issued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  rw [scopeEq]
  exact CallableOrdinaryAnnotationCoherence.ledger_frame_eq_of_erased
    wellFormed samePlan selectedOrigin canonicalOrigin
    (erased.symm.trans (congrArg eraseRequirements canonicalSourceEq))

/-- Construct ports for this exact certificate in the combined registry.
The full original policy receipt is retained independently of the body recipe. -/
private theorem calls_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function scope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context code.reasonAt rootScope rootId rootCode) :
    CallsReady (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected, ready⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalCallsReady.canonical_calls_ready
      code retained metadata sourceReceipt unique typed root
  have guardFrame := selected_frame stagePrepared accepted wellFormed signatureMember sourceOwner
    issued sourceReceipt selected
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  obtain ⟨port⟩ := ready compiler path
  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound }⟩

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}

/-- Static sequence grammar and conditions at one exact Code and BodyWith
context. Conditions may depend on the authentic compiler choice, which the
consumer constructs. Ordinary owner membership is a supported-family
restriction; this does not establish coverage for implementation methods. -/
structure OrdinarySequence {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (named : CallableIndexedNamedGeneration.Named)
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults) where
  shape : CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape code.view function.body
  conditions : (choice : Choice code (stages := (RecursiveNamedPreparedStageScopes.registry stagePrepared))) → Conditions code body choice
  readFuel : ∀ choice, (conditions choice).readFuel = compiled.indexed.fuel
  retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code
  metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
    compiled.indexed named function.source
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : function.source.owner = signature.id

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- Ordinary Associations supply static producer conditions at their own Code.
Principal Associations retain their existing dependent packet/support pair;
they are not required to have an ordinary function declaration owner. -/
def OrdinarySequenceFor {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      OrdinarySequence stagePrepared support.caller.named code support.body
  | .principal _ _ _ _ _ _ _ _ _ _ _ =>
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared), SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet

private theorem sequence_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
    (packet : OrdinarySequence stagePrepared named code body)
    (choice : Choice code (stages := (RecursiveNamedPreparedStageScopes.registry stagePrepared)))
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.Ready
      code body choice (packet.conditions choice) := by
  intro invocation selected
  let static := CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.static
    code body choice (packet.conditions choice) invocation selected
  refine ⟨?_⟩
  intro expression child used
  have typed := (static.authority expression child used).typed
  have certificate := static.certificate expression child used
  have atIndices (readFuel : Nat) (reasonAt : ExpressionId → Word)
      (sameFuel : readFuel = compiled.indexed.fuel) (sameReason : reasonAt = code.reasonAt)
      (root : Certificate code.policy code.lowerBody code.compilation readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source body.toContext.context reasonAt
        (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code) expression child) :
      CallsReady (compiled := compiled) (invocation := invocation) root := by
    subst readFuel
    subst reasonAt
    exact calls_ready stagePrepared code packet.retained packet.metadata sourceReceipt body.unique
      accepted wellFormed packet.signatureMember packet.sourceOwner selected typed root
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  exact atIndices (packet.conditions choice).readFuel choice.packet.reasonAt
    (packet.readFuel choice) choice.reason certificate compiler path

/-- Construct ordinary packet/support using preparation and retain the exact
principal fallback. The resulting family feeds the existing numeric theorem. -/
private theorem sequence_coverage
    (family : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    Nonempty (Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared), SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet) := by
  have input := family association
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      let association := Association.ordinary owner captured code history support origin prefixContext
        globals referenceIndex typed provenance
      obtain ⟨sidecar, _issued, selected⟩ :=
        CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
      have shape : ShapeFor association := input.shape
      obtain ⟨chosen⟩ := choose_for association shape
        (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
      have ready := sequence_ready stagePrepared code support.body input chosen
        support.source_receipt accepted wellFormed
      exact ⟨⟨packet_for association chosen,
        support_for association chosen (input.conditions chosen) ready⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact ⟨input⟩

section Caller
variable {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      headers keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

variable {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {named : CallableIndexedNamedGeneration.Named}
  (code : Code compiled.indexed function localScope administrative)
  (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
  (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
    compiled.indexed named function.source)
  (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
    code.compilation.owner code.active function.source)
  (unique : NodeOccurrencesUnique function.source)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
  {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  (conditions : OriginalConditions compiled code.policy code.compilation compiled.indexed.fuel context invocation
    code.reasonAt rootScope semanticFaults)
  (syntaxTree : Syntax invocation.source rootId)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
  (typed : ExpressionHasType invocation.source context rootId node.type)
  {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody compilerFuel
    code.compilation invocation.source rootScope rootId code.reasonAt = .ok rootCode)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry
  (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver profile observations extension semantic family namedTerminals namedSupport
  acceptedPlan wellFormed retained metadata sourceReceipt unique signatureMember sourceOwner
  selected conditions syntaxTree found typed accepted in
/-- The accepted ordinary caller and prepared ordinary sequence bodies feed
numeric preservation, with the original principal and named static support. -/
theorem preserves_compiled (size : Nat) :
    PreservesAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation (Point rootScope rootId rootCode) callFaults size := by
  have sourceEq : invocation.source = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  have metadataAt : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named invocation.source := by
    rw [sourceEq]
    exact metadata
  have policyFor := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadataAt rootScope code.reasonAt
  let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    conditions.unique conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted
  have ready : CallsReady (compiled := compiled) (invocation := invocation) root :=
    calls_ready stagePrepared code retained metadata sourceReceipt unique
    acceptedPlan wellFormed signatureMember sourceOwner selected typed root
  intro current expression emitted point
  exact CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds.preserves_compiled
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (wellFormed := conditions.wellFormed) (runtime := conditions.runtime)
    (covers := conditions.covers) (unique := conditions.unique)
    (actualFunctionType := conditions.actualFunctionType) (observations := observations)
    (extension := extension) (semantic := semantic)
    (closureCoverage := sequence_coverage stagePrepared family acceptedPlan wellFormed)
    (namedTerminals := namedTerminals) (namedSupport := namedSupport)
    (sameLedger := conditions.sameLedger) (runtimeLedger := conditions.runtimeLedger)
    (uninitialized := conditions.uninitialized)
    conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted ready size point

include bridge receiver profile observations extension semantic family namedTerminals namedSupport
  acceptedPlan wellFormed retained metadata sourceReceipt unique signatureMember sourceOwner
  selected conditions syntaxTree found typed accepted in
/-- The same actual caller and ordinary sequence producer feed numeric
reflection, retaining the original principal and named static support. -/
theorem reflects_compiled (size : Nat) :
    ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation (Point rootScope rootId rootCode) callFaults size := by
  have sourceEq : invocation.source = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  have metadataAt : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named invocation.source := by
    rw [sourceEq]
    exact metadata
  have policyFor := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadataAt rootScope code.reasonAt
  let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    conditions.unique conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted
  have ready : CallsReady (compiled := compiled) (invocation := invocation) root :=
    calls_ready stagePrepared code retained metadata sourceReceipt unique
    acceptedPlan wellFormed signatureMember sourceOwner selected typed root
  intro current expression emitted point
  exact CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds.reflects_compiled
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (wellFormed := conditions.wellFormed) (runtime := conditions.runtime)
    (covers := conditions.covers) (unique := conditions.unique)
    (actualFunctionType := conditions.actualFunctionType) (observations := observations)
    (extension := extension) (semantic := semantic)
    (closureCoverage := sequence_coverage stagePrepared family acceptedPlan wellFormed)
    (namedTerminals := namedTerminals) (namedSupport := namedSupport)
    (sameLedger := conditions.sameLedger) (runtimeLedger := conditions.runtimeLedger)
    (uninitialized := conditions.uninitialized)
    rfl conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted ready size point

end Caller

section PublicRoot
variable {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      headers keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  {beforePlan : SourceCompilationPlan.Plan} {planFuel planBudget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram beforePlan planFuel planBudget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) headers root header)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "rootBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- The actual cached root consumes the mixed numeric family. Ordinary closure
packets come from preparation, and the selected named packet supplies its own
static roots. The exact optional-cell read, parameter entry, body, restoration
and root argument packing are all executed by the existing producers. -/
theorem preserves_root
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments outcome after) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial root.body
            (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
          .done value finalStore) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared),
        SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet :=
    fun association => Classical.choice (sequence_coverage stagePrepared family acceptedPlan wellFormed association)
  let packet := namedTerminals header selected.member
  have children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow
        (headers := headers) (keys := keys) header rootModel
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child packet.certificate rootFaults size := by
    intro child childSelected
    cases namedSupport header selected.member with
    | recursive static =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow.pool
        intro childSize _smaller current id lowered point
        rw [static.point] at point
        exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
          (profile := profile) (closurePackets := fun association => (chosen association).1)
          (closureSupport := fun association => (chosen association).2)
          (namedTerminals := namedTerminals) (namedSupport := namedSupport)
          (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
          (extension := extension) (semantic := semantic) childSize
          (static.roots child childSelected).val point
    | formation static =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.preserves
          (profile := profile) (faults := rootFaults) static childSelected size
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner selected.member
  let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.preserves_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (capture := nativeCapture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (sourceAt := sourceAt) (terminal := packet.receipt) (certifies := packet.certifies)
      packet.layouts selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size children trace (Nat.le_refl _)
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  have read := OptionalCell.read_success Word.zero
    (show Evaluates
      (DataPatternValues.packValues payloads :: payloads.reverse ++
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (.var (header.slot + root.types.length + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) store
      from .var actualReference) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated read result.1
  have rootEvaluation : Evaluates
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      store root.body value finalStore := by
    simpa only [selected.shape.2] using called
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel rootEvaluation
  exact ⟨nativeCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- A completed original root exposes its exact cached named body. Numeric
reflection supplies the staged application and actual returned pool; a staged
rejection remains a staged rejection rather than an ordinary Dynamic fault. -/
theorem reflects_root
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body
        (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
      .done value finalStore) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) arguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared),
        SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet :=
    fun association => Classical.choice (sequence_coverage stagePrepared family acceptedPlan wellFormed association)
  let packet := namedTerminals header selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner selected.member
  let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  rw [selected.shape.2] at measured
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated actualReference capture.read measured
  have children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow
        (headers := headers) (keys := keys) header rootModel
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child packet.certificate rootFaults size := by
    intro child childSelected
    cases namedSupport header selected.member with
    | recursive static =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow.pool
        intro childSize _childSmaller current id lowered point
        rw [static.point] at point
        exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
          (profile := profile) (closurePackets := fun association => (chosen association).1)
          (closureSupport := fun association => (chosen association).2)
          (namedTerminals := namedTerminals) (namedSupport := namedSupport)
          (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
          (extension := extension) (semantic := semantic) rfl childSize
          (static.roots child childSelected).val point
    | formation static =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.reflects
          (profile := profile) (faults := rootFaults) static childSelected size
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.reflects_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (capture := nativeCapture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (prepared := packet.prepared) (aligned := packet.aligned) (stagePrepared := stagePrepared)
      (descriptor := descriptor) (sourceAt := sourceAt) (terminal := packet.receipt) (certifies := packet.certifies)
      packet.layouts selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size children bodyEvaluation (Nat.le_of_lt smaller)
  exact ⟨nativeCapture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩

variable {recipe : SourceCoreIndexedSession.Recipe} {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {options : SourceCoreExecution.RunOptions}
  (sameCompiled : recipe.compiled = compiled)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe (sameCompiled.symm ▸ root)
    world store payloads encodedValues)

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- An actual public success reaches the same cached named body and staged
Source application. Export metadata and the body model's receiving metadata
retain their own actual receipts; no registry equality is invented. -/
theorem public_run_succeeded_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- Public failure retains the actual staged failure relation. In particular,
a nested stage rejection is not relabeled as a Dynamic semantic fault. -/
theorem public_run_failed_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    failed, sessionAt, trace, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- A staged Source Word result is preserved by the same public checkpoint
at sufficient native fuel. The actual export budget remains independent of
the input budget and the staged trace is retained unchanged. -/
theorem public_word_preserved
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments (.value (.word word)) after) :
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context (.value (.word word)) after
          (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    preserves_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) trace
  have represented := result.2.1
  rw [outputWord] at represented
  have nativeWord : value = .inRight .word (.word word) := by
    cases represented with
    | value payload =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨capture, finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => RecursiveNamedPublicExecutionMeaning.resume_word_succeeded
      atCheckpoint resumed (started.initial.native_done_iff.mpr (completes fuel enough)) requested positive,
    result⟩

end PublicRoot

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
