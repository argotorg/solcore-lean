import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection

/-!
# Selected compilations: ordinary rows calling methods

Scoped method roots and terminal support of ordinary rows, and their coerced direct roots.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryClosureFacts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryClosureFacts
open Core Frontend SourceInference

/-- The retained caller's real target and cache record identify its selected
original definition, including an invocation outside the current inventory. -/
theorem certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (caller : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt header context evidence) :
    SelectedCompilationNamedSourceTyping.Certified header := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _resolved, accepted⟩ := caller.prepared.origin
  have valid := bodies.ordinary generic
    ⟨caller.prepared.index, caller.prepared.named, signature, request.parameterSubstitution,
      caller.prepared.selected, signatureMember, genericMember,
      by simpa only [caller.prepared.same] using accepted⟩
  have matched := CallableNamedMetadata.matches_of_exact header.target
    (CallableIndexedActualNamedSourceReceipts.header_record compiled header)
  have owner : (FunctionDefinition.ofChecked generic).body.owner = header.instantiation.declaration :=
    (RecursiveNamedSpecializationBodyFacts.identities accepted).2.2.symm.trans matched.declaration
  obtain ⟨types, lexical, facts, certificate⟩ :=
    header.frame.instantiated.certificate_of_valid bodies.signatures bodies.function_ids
      (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certificate.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryClosureFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryEvidenceCallsReady
/-! Static indirect-call authority at every genuine selected ordinary closure
scope. Direct and builtin ancestors retain their actual recursive argument
paths; original Source typing and the prepared guard frame determine each port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryEvidenceCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  {readFuel callFuel : Nat} {context : SourceSemantics.Context}
  {callScope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {lowered : SourceCoreBasic.LoweredExpr}
  (readPolicy : code.policy.readExpression function.source id =
    SourceCoreCompatibleDataExpressions.readExpression
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked function.source id)
  (compiler : CallableIndirectCallCertificates.Receipt code.policy code.lowerBody callFuel
    code.compilation function.source callScope id callee ids metadata code.reasonAt lowered)
  (typed : ExpressionHasType function.source context id compiler.original.type)

include readPolicy typed in
/-- Recover the actual full owner, original Source view and guard frame from
one Code's authentic stage producer. No invocation or sidecar is chosen by
an execution premise, and the emitted compiler receipt stays unchanged. -/
private theorem canonical_scope_port
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram
      compiled.indexed.base.plan code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code source unique
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent
    compiler readPolicy
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler readPolicy code.active code.callables
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, bundle, resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique typed
  obtain ⟨calleeNode, contains, stored⟩ := calleeTyped.stored_type
  have calleeFound := lookupExpression?_complete unique contains
  have sourceEq := source.source issued
  have originalUnique : NodeOccurrencesUnique sidecar.source := by
    have substituted : NodeOccurrencesUnique (sidecar.source.applySubstitution code.active) :=
      sourceEq ▸ unique
    change ((sidecar.source.applySubstitution code.active).nodes.map Node.occurrenceId).Nodup
      at substituted
    change (sidecar.source.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using substituted
  let port : CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler := {
    prepared := prepared
    sidecar := sidecar
    caller := by rw [prepared.caller]; exact issued
    view := Or.inr ⟨code.active, sourceEq⟩
    guardFrame := rfl
    originalUnique := originalUnique
    sourceParent := parent
    calleeNode := calleeNode
    calleeFound := calleeFound }
  exact ⟨sidecar, issued, selected, ⟨port⟩⟩


variable (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

/-- The selected frame comes from the actual accepted preparation. The original
compiler certificate supplies the exact indirect-call path, even beneath a
direct declaration or builtin call. -/
theorem calls_ready {directSites : DeclarationInstantiation → Prop}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function scope administrative)
    (readPolicy : ∀ id, GeneralSyntax function.source id directSites →
      code.policy.readExpression function.source id =
      SourceCoreCompatibleDataExpressions.readExpression
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked function.source id)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner compiled.sourceProgram function.source.owner)
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
      invocation.source context code.reasonAt rootScope rootId rootCode)
    (rootSyntax : GeneralSyntax invocation.source rootId directSites) :
    CallsReady (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code sourceReceipt unique
  have guardFrame := SelectedCompilationScopeCoherence.selected_frame stagePrepared accepted bodies.signatures bodies.function_ids atOwner signatureMember sourceOwner
    issued sourceReceipt selected
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path rootSyntax
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨actualSidecar, actualIssued, _actualSelected, ⟨port⟩⟩ :=
    canonical_scope_port code (readPolicy _ syntaxTree) compiler parentTyped sourceReceipt unique
  have same : actualSidecar = canonical := Except.ok.inj (actualIssued.symm.trans issued)
  cases same

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

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryEvidenceCallsReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedRoots
/-! Each actual ordinary lexical callback keeps its original Source context,
physical scope and retained Code. General expression certificates are recovered
from the real view compiler; finite direct/index authority stays static. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
open CallableIndexedOwnedPreparedStagedOrdinaryMethodPolicy
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open SelectedCompilationRootStaticSupport
open SelectedCompilationMixedRootSupport (Root)

section Generic
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
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
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
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The actual binder fields transport typing, ledger and evidence. The root
retains the concrete Code compiler, including its original prefix and reasons. -/
theorem of_original_child_with_catalog
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
  have atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner compiled.sourceProgram function.source.owner := by
    obtain ⟨caller⟩ := provenance.body_caller_receipt
    rw [support.source]
    exact SelectedCompilationOrdinaryAnnotationCoherence.at_prepared bodies caller.prepared
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    SelectedCompilationOrdinaryEvidenceCallsReady.calls_ready stagePrepared
      code (fun id tree => retained_read_policy provenance.policy_recipe metadata tree) support.source_receipt support.unique
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) bodies atOwner signatureMember sourceOwner
      selected childTyped certificate childTree
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation
        (.initial compiled.compatible.checked) child.source callScope callId callee ids
        instantiation code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        headers context child.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
          SelectedCompilationSourceSignatureFacts.Shape port.header} := by
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
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context child.evidence⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
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
          (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
      exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared signatures ledger assumptions idsUnique caller.dictionary⟩,
        SelectedCompilationCatalog.certificates bodies rows port.header port.member,
        SelectedCompilationSourceSignatureFacts.Shape.of_inventory bodies rows port.header port.member⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        code.policy code.lowerBody callFuel code.compilation (.initial compiled.compatible.checked)
        child.source callScope callId code.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty {port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context child.evidence stages //
        Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context child.evidence
          port.principal.traitName port.principal.methodName compiler.node.requirements
          port.principal.sourceBody port.principal.dictionary} := by
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
        (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
    have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique childTyped path
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
    exact SelectedCompilationMethodSelectionIssuer.of_actual compiler actual compiler.special
      sourceReceipt methods checked bodies catalog
      (by rw [support.compilation]; exact SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      (by rw [support.compilation]; exact callerMember) nodeMember
      (by rw [support.compilation]; rfl) (by rw [support.compilation]; rfl)
      signatures ledger assumptions idsUnique dictionary unique parentTyped stagePrepared
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
    catalog := bodies.signatures
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

include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The real body-view callback supplies a root for the original Source at its
actual lexical context, using the unchanged compiler and retained dictionary. -/
theorem of_child_with_catalog
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
  exact of_original_child_with_catalog stagePrepared code support provenance receiver bodies certified supported metadata
    rows covered checked catalog methods signatureMember sourceOwner selected fields declarations tree reached found typed
    (CallableIndexedOwnedPreparedStagedMethodBodyViewTransport.accepted_original
      code provenance.policy_recipe provenance.body_view callables metadata tree reached accepted)

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodTerminalSupport
/-! The genuine retained ordinary terminal body supplies each selected mixed
root with its complete caller dictionary and actual method selection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
section Generic
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
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
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
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The accepted terminal callback yields the original method-aware expression
root at every genuine selected Source scope. -/
theorem of_actual_with_catalog
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (tree : GeneralSyntax function.source expression directSites)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨node, found, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  obtain ⟨⟨actualType, root⟩⟩ :=
    SelectedCompilationOrdinaryMethodScopedRoots.of_child_with_catalog stagePrepared code support provenance
      receiver bodies certified supported metadata rows covered checked catalog methods signatureMember sourceOwner
      selectedAt (Dynamic.RuntimeContextFields.refl _)
      (by simpa only [sameSource] using declarations)
      (expressionEq.symm ▸ tree)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) accepted
  have sameNode := Option.some.inj (root.found.symm.trans found)
  have resultEq : actualType = function.resultType := root.rawResult.symm.trans (sameNode ▸ rawType)
  exact ⟨resultEq ▸ root⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedSupport
/-! General expressions at actual ordinary lexical scopes retain the same
Code compiler and genuine canonical-root authorities. Existing branching
collector/flow trees handle local allocation, assignment and finite control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open SelectedCompilationMixedRootSupport (Root)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem accepted_child
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
    {stages : Staging.Recursive.Registry}
    (choice : CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.Choice code (stages := stages))
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (min fuel code.fuel)
      code.compilation code.view current id code.reasonAt = .ok lowered := by
  have callback := choice.callback
  have reason := choice.reason
  rw [callback, reason] at accepted
  exact accepted


section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include provenance receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
/-- Every original expression is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_general_with_catalog
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := certified
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨support.body.frame, support.body.projection, compiled.indexed.fuel, ?_,
    choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  · rw [support.compilation]; rfl
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact bodies.signatures)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context scope id lowered => Nonempty (Σ rawType,
      Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
        context child code.reasonAt scope id lowered rawType faults))
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType _native => by
      exact SelectedCompilationOrdinaryMethodScopedRoots.of_child_with_catalog
        stagePrepared code support provenance receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner
        selected fields declarations tree reached found typed (accepted_child code choice accepted))
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [(stages).source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance receiver bodies certified supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_actual_with_catalog
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨choice.packet,
    support_general_with_catalog stagePrepared code support provenance receiver bodies certified supported original rows covered checked catalog methods
      signatureMember sourceOwner choice choiceIssued syntaxTree⟩⟩

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryMethodScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedDirectRoots
/-! Original direct output coercions retain the real caller, ordered argument
compiler actions, and selected conversion packets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedDirectRoots
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
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
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


include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance in
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
  obtain ⟨originalCaller⟩ := provenance.body_caller_receipt
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
    obtain ⟨⟨rawType, root⟩⟩ := SelectedCompilationOrdinaryMethodScopedRoots.of_original_child_with_catalog
      stagePrepared code support provenance receiver bodies certified (fun _ impossible => False.elim impossible)
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
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedDirectRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedTerminalSupport
/-! The authentic retained terminal callback yields an original coerced root
at every selected Source scope. Body-view transport keeps the complete parent
node and composes the actual ordered argument compiler actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
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



include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance in
theorem of_actual
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

    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (found : function.source.lookupExpression? expression = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = expression)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  subst expression
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨actualNode, actualFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have originalFound : function.source.lookupExpression? packet.expression = some actualNode := by
    simpa only [sameSource] using actualFound
  cases Option.some.inj (originalFound.symm.trans found)
  have reached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  generalize fuelEq : min packet.receipt.childFuel code.fuel = fuel at accepted
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
      have original := CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_original
        code provenance.policy_recipe provenance.body_view callables
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor.of_native metadata)
        noInitializer found form requirements children reached accepted
      obtain ⟨root⟩ := SelectedCompilationOrdinaryCoercedDirectRoots.of_original_child
        stagePrepared code support provenance receiver bodies certified metadata rows checked catalog methods
        signatureMember sourceOwner methodBodies selectedAt (Dynamic.RuntimeContextFields.refl _)
        (by simpa only [sameSource] using declarations) children reached found form nonempty requirements
        noInitializer supported covered (by simpa only [sameSource] using typed) original
      refine ⟨.coercedDirect ?_⟩
      simpa only [rawType] using root

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryCoercedTerminalSupport
end
