import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryMethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport

/-! Original direct output coercions retain the real caller, ordered argument
compiler actions, and selected conversion packets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedDirectRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open SelectedCompilationMixedRootSupport (Root CoercedDirectRoot CoercionMethods)

private theorem arguments_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (typed : ExpressionHasType source context id node.type) :
    ∃ types, ExpressionsHaveTypes source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst_vars
    rw [form] at raw
    cases raw with
    | directCall _ _ arguments => exact ⟨_, arguments⟩

private theorem output_path {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type) :
    CoercionPathValid context node.rawType node.type node.coercions := by
  obtain ⟨actual, rawType, contains, result, raw, _admissible, path⟩ := typed.raw_type_and_output_path
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  simpa only [← raw] using path

private theorem argument_tree {source : TypedSource} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (compile : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM compile = .ok codes)
    (extract : ∀ id ∈ ids, ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → compile id = .ok code → certificate scope id code) :
    ∃ actualTypes, DataExpressionSequence.Tree source certificate scope ids actualTypes codes := by
  induction ids generalizing types codes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨[], .nil⟩
  | cons id ids ih =>
    cases typed with
    | cons head tail =>
      cases first : compile id with
      | error error => simp [List.mapM_cons, first, bind, Except.bind] at accepted
      | ok code =>
        cases rest : ids.mapM compile with
        | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at accepted
        | ok restCodes =>
          simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst codes
          obtain ⟨node, contains, typeEq⟩ := head.stored_type
          have found := lookupExpression?_complete unique contains
          have child := extract id (by simp) node code found (typeEq ▸ head) first
          obtain ⟨tailTypes, tailTree⟩ := ih tail rest (fun id member => extract id (by simp [member]))
          cases tailTree with
          | nil => exact ⟨_, .single found child⟩
          | single nextFound nextChild => exact ⟨_, .cons found child (.single nextFound nextChild)⟩
          | cons nextFound nextChild tailTree => exact ⟨_, .cons found child (.cons nextFound nextChild tailTree)⟩

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_original_child
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = id)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (fuel+1)
      code.compilation function.source current id code.reasonAt = .ok lowered) :
    Nonempty (CoercedDirectRoot compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered node.type faults) := by
  have sameSource := (stages).source selected
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  have authentic : SourceCoreEvidence.lowerWithProjector compiled.sourceProgram
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType
      support.caller.named.specialized code.compilation
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child code.policy code.lowerBody fuel code.compilation)
      (fuel+1) child.source current id code.reasonAt code.policy.callables = .ok (some lowered) := by
    obtain ⟨diagnostics, namedCode, compilation, rootFuel, _body, recipe, sameCompilation⟩ := provenance.policy_recipe
    rw [sameCompilation] at accepted ⊢
    rw [sameSource, callables]
    rcases CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_direct_action
      recipe noInitializer found form accepted with bypass | actual
    · exact False.elim (requirements (CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass).1)
    · simpa only [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] using actual
  have childFound : child.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted childFound form authentic
  let originalCaller := callerReceipt.extend (Dynamic.MonoBindersExtend.runtimeContextFields support.body.extended)
  let caller := (originalCaller.extend fields).with_evidence ((stages).evidence selected)
  have parameters := RecursiveNamedInitialContextValidity.mono_fields support.caller.extended
  have signatures : context.signatures = compiled.sourceProgram.signatures := by
    rw [caller.fields.signatures, parameters.signatures, caller.aligned.function]
    rfl
  have ledger : context.solvedRequirements = support.caller.named.specialized.function.solvedRequirements :=
    caller.fields.solvedRequirements.trans (support.caller.valid.ledger.trans
      (caller.aligned.solved.trans (congrArg (fun named => named.specialized.function.solvedRequirements) caller.aligned.named.symm)))
  have assumptions : ∀ goal, goal ∈ support.caller.named.specialized.assumptions → goal ∈ context.assumptions := by
    intro goal member
    rw [caller.fields.assumptions, parameters.assumptions, caller.aligned.function]
    change goal ∈ caller.prepared.named.specialized.assumptions
    rw [← caller.aligned.named]
    exact member
  have idsUnique : RequirementIdsUnique context := by
    simpa only [RequirementIdsUnique, caller.fields.solvedRequirements] using
      (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
  have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
    have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
    rw [caller.dictionary, same]
    rfl
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedRawDirectAuthority.of_resolved actual rows supported
    (covered actual.native.index actual.native.signature
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.target actual)
      (CallableIndexedOwnedPreparedStagedRawDirectAuthority.native_selected actual).1)
    (by rw [support.compilation]; rfl)
    ⟨actual.available, actual.resolved, dictionary⟩ signatures ledger assumptions idsUnique
  have childTyped : ExpressionHasType child.source context id node.type := by simpa only [sameSource] using typed
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ support.unique
  have callerMember := (CallableNamedMetadata.specialization_of_exact
    (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)).1
  have nodeMember : .expression node ∈ support.caller.named.specialized.function.typedBody.nodes := by
    have lookup : support.caller.named.specialized.function.typedBody.lookupExpression? id = some node := by
      have sourceEq : function.source = support.caller.named.specialized.function.typedBody := support.source
      rw [← sourceEq]
      exact found
    exact (lookupExpression?_sound lookup).1
  obtain ⟨calls, spine⟩ := CallableCoercionSpine.of_accepted actual.suffix.accepted
  obtain ⟨⟨chain, certifiedChain⟩⟩ := SelectedCompilationCoercionChainIssuance.of_spine methods checked bodies catalog
    (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    (by rw [support.compilation]; exact callerMember) nodeMember
    (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
    signatures ledger assumptions actual.resolved idsUnique dictionary stagePrepared spine
    (output_path unique childFound childTyped) (fun step member => List.mem_append_left _ member)
  have methodPackets : ∀ {src tgt input output steps calls} (selectedChain :
      CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled
        ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext support.caller.named.signature.key []).expressions.projectType code.compilation
        support.caller.named.specialized actual.available current node code.policy.callables context child stages
        src tgt input steps output calls), SelectedCompilationCoercionChainIssuance.Certified stagePrepared selectedChain →
        CoercionMethods headers faults selectedChain := by
    intro src tgt input output steps calls selectedChain certificates
    induction selectedChain with
    | nil => trivial
    | cons head port valid tail ih =>
      obtain ⟨headCertified, tailCertified⟩ := certificates
      obtain ⟨packet, same, supported⟩ := methodBodies port.principal port.sourceAt ⟨port.diagnostics⟩ headCertified
      exact ⟨⟨packet, same, same.symm ▸ headCertified, supported⟩, ih tailCertified⟩
  let certificate : GenericExpressionMeaning.Certificate := fun current id lowered =>
    ∃ rawType, Nonempty (Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context child code.reasonAt current id lowered rawType faults)
  obtain ⟨rawTypes, argsTyped⟩ := arguments_typed unique childFound form childTyped
  have argumentsAccepted : ids.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy
      code.policy code.lowerBody fuel code.compilation child.source current argument code.reasonAt) = .ok actual.loweredArguments := by
    simpa only [CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child, Nat.min_eq_right (Nat.le_succ fuel)] using actual.argumentsAccepted
  obtain ⟨argumentTypes, argumentTree⟩ := argument_tree (certificate := certificate) _ unique argsTyped argumentsAccepted (by
    intro argument member argumentNode argumentCode argumentFound argumentTyped argumentAccepted
    obtain ⟨⟨rawType, root⟩⟩ := SelectedCompilationPreparedOrdinaryMethodScopedRoots.of_original_child_with_catalog
      stagePrepared code support provenance callerReceipt receiver bodies certified (fun _ impossible => False.elim impossible)
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor.of_native metadata) rows
      (fun _ impossible => False.elim impossible) checked catalog (.generic ⟨methods.formed, methods.assumptions⟩)
      signatureMember sourceOwner selected fields declarations (children argument member)
      (.expression reached found (by simp [form, ExpressionForm.references, member]))
      (by simpa only [sameSource] using argumentFound) (by simpa only [sameSource] using argumentTyped)
      (by simpa only [sameSource] using argumentAccepted)
    exact ⟨rawType, ⟨root⟩⟩)
  exact ⟨{
    compilerFuel := fuel+1
    accepted := by simpa only [sameSource] using accepted
    project := _
    caller := support.caller.named.specialized
    child := _
    fuel := fuel+1
    node := node
    callee := callee
    arguments := ids
    instantiation := instantiation
    actual := actual
    nonempty := nonempty
    result := rfl
    typed := childTyped
    port := port
    certified := SelectedCompilationCatalog.certificates bodies rows port.header port.member
    shape := SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member
    argumentTypes := argumentTypes
    argumentCertificate := certificate
    argumentTree := argumentTree
    argumentRoots := fun proof => proof
    calls := calls
    chain := chain
    methods := methodPackets chain certifiedChain
    ledger := ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    catalog := bodies.signatures
    runtime := by
      rw [sameSource]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.toContext.extended).1).transport fields
    covers := by rw [(stages).evidence selected]; exact fields.covers support.body.valid.covers
  }⟩
end Actual
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedDirectRoots
