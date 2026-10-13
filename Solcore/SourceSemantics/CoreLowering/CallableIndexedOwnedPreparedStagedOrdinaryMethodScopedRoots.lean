import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryEvidenceCallsReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyViewTransport

/-! Each actual ordinary lexical callback keeps its original Source context,
physical scope and retained Code. General expression certificates are recovered
from the real view compiler; finite direct/index authority stays static. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
open CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (Root)

variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include receiver wellFormed supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The actual binder fields transport typing, ledger and evidence. The root
retains the concrete Code compiler, including its original prefix and reasons. -/
theorem of_original_child
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have originalProfile := retained_policy_for provenance.policy_recipe metadata callables supported current code.reasonAt
  have profile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodStepPolicyFor
      code.policy code.compilation compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source current code.reasonAt directSites := by simpa only [sameSource] using originalProfile
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have childTree : GeneralSyntax child.source id directSites := by simpa only [sameSource] using tree
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source current context := by
    simpa only [sameSource] using declarations
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation child.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable code.active code.callables
    unique childDeclarations profile coercions childTree childFound childTyped compiledChild
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    CallableIndexedOwnedPreparedStagedOrdinaryEvidenceCallsReady.calls_ready stagePrepared
      code (fun id tree => retained_read_policy provenance.policy_recipe metadata tree) support.source_receipt support.unique
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed signatureMember sourceOwner
      selected childTyped certificate childTree
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation
        (.initial compiled.compatible.checked) child.source callScope callId callee ids
        instantiation code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        headers context child.evidence) := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path childTree
    have site := actualTree.direct_site compiler.metadata.found compiler.form
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
      (covered instantiation site compiler.index compiler.signature compiler.target compiler.global)
      (by rw [support.compilation]; rfl)
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    rcases retained_accepted_direct_action provenance.policy_recipe childMetadata actualTree
      compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (retained_direct_hook provenance.policy_recipe childMetadata actualTree
          compiler.metadata.found compiler.form callback budget callScope code.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (retained_read_policy provenance.policy_recipe childMetadata actualTree)
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context child.evidence⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      obtain ⟨originalCaller⟩ := provenance.body_caller_receipt
      let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
      have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
      have signatures : context.signatures = compiled.sourceProgram.signatures := by
        rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
        rfl
      have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
        caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
          (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
            caller.aligned.named.symm)))
      have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
        intro goal member
        rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
        change goal ∈ caller.prepared.named.specialized.assumptions
        rw [← caller.aligned.named]
        exact member
      have idsUnique : RequirementIdsUnique context := by
        simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
          (RecursiveNamedInitialContextValidity.scoped_ledger support.caller.frame support.caller.extended wellFormed).idsUnique
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared signatures ledger assumptions idsUnique caller.dictionary⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation (.initial compiled.compatible.checked)
        child.source callScope callId code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context child.evidence stages) := by
    intro callFuel callScope callId callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path childTree
    have childMetadata : MetadataFor compiled.indexed support.caller.named child.source directSites := by
      simpa only [sameSource] using metadata
    have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
        (∃ operator left right, compiler.node.form = .binary left operator right) := by
      rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩
    have hook := retained_operator_hook provenance.policy_recipe childMetadata actualTree compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody callFuel code.compilation)
      (callFuel + 1) callScope code.reasonAt
    have acceptedMethod := hook.symm.trans compiler.special
    have nonempty : compiler.node.requirements ≠ [] := by
      intro empty
      exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
    obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
      nonempty acceptedMethod
    rw [← callables] at actual
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted actual
    let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic compiler actual compiler.special
    have selectionSupport := CallableIndexedOwnedPreparedStagedClosedMethodSelection.selection_support
      authentic checked wellFormed methods sourceReceipt
    obtain ⟨originalCaller⟩ := provenance.body_caller_receipt
    let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
    have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
    have signatures : context.signatures = compiled.sourceProgram.signatures := by
      rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
      rfl
    have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
      caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
        (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements)
          caller.aligned.named.symm)))
    have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
      intro goal member
      rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
      change goal ∈ caller.prepared.named.specialized.assumptions
      rw [← caller.aligned.named]
      exact member
    have idsUnique : RequirementIdsUnique context := by
      simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
        (RecursiveNamedInitialContextValidity.scoped_ledger support.caller.frame support.caller.extended wellFormed).idsUnique
    have callerMember := (CallableNamedMetadata.specialization_of_exact
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
    have sourceEq : child.source = support.caller.named.specialized.function.typedBody :=
      sameSource.trans support.source
    have nodeMember : .expression compiler.node ∈ support.caller.named.specialized.function.typedBody.nodes := by
      have found : support.caller.named.specialized.function.typedBody.lookupExpression? callId = some compiler.node :=
        by simpa only [sourceEq] using compiler.metadata.found
      exact (lookupExpression?_sound found).1
    have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
      have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
      rw [caller.dictionary, same]
      rfl
    exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual compiler actual compiler.special
      sourceReceipt selectionSupport checked wellFormed catalog
      (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      (by rw [support.compilation]; exact callerMember) nodeMember
      (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
      signatures ledger assumptions idsUnique dictionary stagePrepared
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
  exact ⟨⟨node.type, ⟨root, directReady,
    CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.ordinary_ready support provenance.body_reasons
      sameSource reached certificate, methodReady⟩⟩⟩

include receiver wellFormed supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The real body-view callback supplies a root for the original Source at its
actual lexical context, using the unchanged compiler and retained dictionary. -/
theorem of_child
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : GeneralSyntax function.source id directSites)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (Σ rawType, Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults) := by
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  exact of_original_child stagePrepared code support provenance receiver wellFormed supported metadata
    rows covered checked catalog methods signatureMember sourceOwner selected fields declarations tree reached found typed
    (CallableIndexedOwnedPreparedStagedMethodBodyViewTransport.accepted_original
      code provenance.policy_recipe provenance.body_view callables metadata tree reached accepted)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots
