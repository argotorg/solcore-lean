import Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport

/-! Actual named compiler children share physical mixed roots at every lexical
context. Direct calls, trait methods and indirect calls retain the original
caller ledger, full dictionary and actual selected compiler action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax MethodStepPolicyFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open SelectedCompilationMixedRootSupport (RootAt)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include prepared aligned diagnostic receiver bodies certified supported metadata rows covered checked catalog methods in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_policy_sites_with_catalog
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      prepared.named prepared.diagnostics prepared.code prepared.compilation rootFuel
      rootSource rootScope rootId rootReasonAt rootLowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      fuel (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata scope header.reasonAt
  have childProfile : MethodStepPolicyFor root.selected.policy (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt directSites := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode, GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have compiledChild := accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique declarations childProfile coercions tree found typed compiledChild
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _with_catalogMember, _requested, specialized⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities specialized
  have body := RecursiveNamedSpecializationBodyFacts.body specialized
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, aligned.named, prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  have guardFrame := SelectedCompilationScopeCoherence.selected_frame actual
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) bodies.signatures bodies.function_ids
    (by
      have owner : header.function.source.owner = row.function.typedBody.owner := by
        rw [header.agreement.source, aligned.named, prepared.same]
      rw [owner]
      exact SelectedCompilationOrdinaryAnnotationCoherence.at_prepared bodies prepared)
    signatureMember sourceOwner issued sourceReceipt selected
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler path
    have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path tree
    have readPolicy := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy
      root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
    have childRead : root.selected.policy.readExpression invocation.source callId =
        SourceCoreCompatibleDataExpressions.readExpression
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source callId := by
      simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
    have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler childRead
    obtain ⟨callPrepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
      compiler childRead [] root.callables
    have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
      compiler unique typed path
    obtain ⟨parameter, result, types, calleeTyped, _⟩ :=
      CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
        compiler parent unique parentTyped
    obtain ⟨calleeNode, contains, _⟩ := calleeTyped.stored_type
    exact ⟨{
      prepared := callPrepared
      sidecar := sidecar
      caller := by rw [callPrepared.caller]; simpa only [aligned.named, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using issued
      view := .inl (sameSource.trans canonicalSource)
      guardFrame := guardFrame
      originalUnique := canonicalSource ▸ header.unique
      sourceParent := parent
      calleeNode := calleeNode
      calleeFound := lookupExpression?_complete unique contains }⟩
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        (.initial compiled.compatible.checked) invocation.source callScope callId callee ids
        instantiation header.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) context invocation.evidence //
        SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header } := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path tree
    have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
      actualTree compiler.metadata.found compiler.form
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
      (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
    have childMetadata : MetadataFor compiled.indexed prepared.named invocation.source directSites := by
      simpa only [sameSource] using metadata
    rcases CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
      root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook root.compilerPolicy
          childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context invocation.evidence⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      let caller := SelectedCompilationNamedEvidenceScopedCallerFrames.of_selected
        prepared aligned selected fields certified
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        (.initial compiled.compatible.checked) invocation.source callScope callId header.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty { port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context invocation.evidence stages //
        Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
          port.principal.traitName port.principal.methodName compiler.node.requirements
          port.principal.sourceBody port.principal.dictionary } := by
    intro callFuel callScope callId methodCode compiler path
    have originalTree := tree
    have childMetadata : MetadataFor compiled.indexed prepared.named invocation.source directSites := by
      simpa only [sameSource] using metadata
    have actionTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path originalTree
    have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
        (∃ operator left right, compiler.node.form = .binary left operator right) := by
      rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩
    have hook := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.operator_hook
      root.compilerPolicy childMetadata actionTree compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy root.selected.lowerBody
        callFuel (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)) (callFuel+1) callScope header.reasonAt
    have accepted := hook.symm.trans compiler.special
    have nonempty : compiler.node.requirements ≠ [] := by
      intro empty
      exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
    obtain ⟨action⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
      nonempty accepted
    rw [← root.selected.callables] at action
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
    obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted action
    let caller := SelectedCompilationNamedEvidenceScopedCallerFrames.of_selected prepared aligned selected fields certified
    have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique typed path
    have callerMember := (CallableNamedMetadata.specialization_of_exact
      (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook)).1
    have sourceEq : invocation.source = prepared.named.specialized.function.typedBody :=
      sameSource.trans (header.agreement.source.trans (congrArg
        (fun named : SourceCoreGeneralFunctions.Function => named.specialized.function.typedBody) aligned.named))
    have nodeMember : .expression compiler.node ∈ prepared.named.specialized.function.typedBody.nodes := by
      have found : prepared.named.specialized.function.typedBody.lookupExpression? callId = some compiler.node :=
        by simpa only [sourceEq] using compiler.metadata.found
      exact (lookupExpression?_sound found).1
    have dictionary : invocation.evidence = CallableNamedMetadata.environment action.available := by
      have same := Except.ok.inj (action.resolved.symm.trans caller.prepared.resolved)
      rw [caller.dictionary, same]
      rfl
    exact SelectedCompilationMethodSelectionIssuer.of_actual compiler action compiler.special
      sourceReceipt methods checked bodies catalog
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      callerMember nodeMember rfl rfl caller.signatures caller.ledger caller.assumptions caller.unique dictionary unique parentTyped actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source := by
    rw [sameSource]
    exact (certified.runtime.transport
      (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  let result : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults := RootAt.ofRoot {
    compilerFuel := fuel
    accepted := accepted
    certificate := certificate
    node := node
    found := found
    rawResult := rfl
    typed := typed
    sameLedger := fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved)
    runtimeLedger := fields.runtimeRequirementLedger
      (SelectedCompilationHeaderFacts.runtime_ledger certified)
    unique := unique
    catalog := bodies.signatures
    runtime := runtime
    covers := by
      rw [(stages).evidence selected]
      exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := fun _ _ _ read _ location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized prepared diagnostic aligned receiver
        (by simpa only [sameSource] using read) location
    callsReady := ready
    directReady := directReady
    indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      prepared diagnostic aligned sameSource certificate
    methodReady := methodReady }
  exact ⟨result, rfl⟩


include prepared aligned diagnostic receiver bodies certified supported metadata rows covered checked catalog methods in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_accepted_sites_with_catalog
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned (by simpa only [sameSource] using accepted)
  exact of_policy_sites_with_catalog prepared aligned diagnostic receiver bodies certified supported metadata rows covered checked catalog methods actual selected
    fields declarations tree found typed root (by simpa only [sameSource] using root.selected.accepted)

end Generic



end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedRoots
