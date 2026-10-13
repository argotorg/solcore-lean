import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (MethodStepPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport (policy_receipt SidecarAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include wellFormed metadata tree rows covered in
/-- Each reached declaration obtains evidence at this exact selected caller
frame, from the same authentic compiler action as the static certificate. -/
theorem direct_ready {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : stages.Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id callee ids instantiation lowered}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id callee ids instantiation header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header.context child.evidence) := by
  intro callFuel callScope id callee ids instantiation lowered compiler path
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by
    simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
  have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
  have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
    actualTree compiler.metadata.found compiler.form
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
    (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
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
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements header.context child.evidence⟩⟩
  · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
      compiler.metadata.found compiler.form authentic
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
      compiler port actual caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩

include wellFormed metadata tree checked catalog methods actualStages in
/-- The original policy is opened at the exact reached method leaf. The
retained compiler program is re-established here from that real recipe. -/
theorem method_ready_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  intro callFuel callScope id lowered compiler path
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
  have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path originalTree
  have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
      (∃ operator left right, compiler.node.form = .binary left operator right) := by
    rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
    · exact .inl ⟨operator, operand, form⟩
    · exact .inr ⟨operator, left, right, form⟩
  have hook := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.operator_hook
    root.compilerPolicy childMetadata actualTree compiler.metadata.found form
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy root.selected.lowerBody
      callFuel (context compiled.indexed terminal.prepared.named)) (callFuel+1) callScope header.reasonAt
  have accepted := hook.symm.trans compiler.special
  have nonempty : compiler.node.requirements ≠ [] := by
    intro empty
    exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
  obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
    (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
    nonempty accepted
  rw [← root.selected.callables] at actual
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
  obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted actual
  let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic compiler actual compiler.special
  let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ header.unique
  obtain ⟨rootNode, _found, _type, originalTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have rootTyped : ExpressionHasType child.source header.context terminal.expression rootNode.type := by
    simpa only [sameSource] using originalTyped
  have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique rootTyped path
  have support := CallableIndexedOwnedPreparedStagedGenericMethodSelection.selection_support
    authentic checked wellFormed methods sourceReceipt caller.signatures caller.ledger caller.assumptions
    unique caller.unique parentTyped
  have callerMember := (CallableNamedMetadata.specialization_of_exact
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled terminal.prepared.selected terminal.prepared.compilation.hook)).1
  have sourceEq : child.source = terminal.prepared.named.specialized.function.typedBody :=
    sameSource.trans (header.agreement.source.trans (congrArg
      (fun named : SourceCoreGeneralFunctions.Function => named.specialized.function.typedBody) terminal.aligned.named))
  have nodeMember : .expression compiler.node ∈ terminal.prepared.named.specialized.function.typedBody.nodes := by
    have found : terminal.prepared.named.specialized.function.typedBody.lookupExpression? id = some compiler.node :=
      by simpa only [sourceEq] using compiler.metadata.found
    exact (lookupExpression?_sound found).1
  have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
    have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
    rw [caller.dictionary, same]
    rfl
  exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual compiler actual compiler.special
    sourceReceipt support checked wellFormed catalog
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    callerMember nodeMember rfl rfl caller.signatures caller.ledger caller.assumptions caller.unique dictionary actualStages
include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry actualStages).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  have available : (header.function.source.lookupExpression? terminal.expression).isSome := by
    obtain ⟨node, found, _⟩ := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
      terminal.receipt selected wellFormed
    exact Option.isSome_of_eq_some found
  let node := (header.function.source.lookupExpression? terminal.expression).get available
  have found : header.function.source.lookupExpression? terminal.expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context terminal.expression node.type := by
    obtain ⟨original, originalFound, rawType, typed⟩ :=
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
    have same := Option.some.inj (originalFound.symm.trans found)
    exact same ▸ ⟨rawType, typed⟩
  have rawType := properties.1
  have typed := properties.2
  have childFound : child.source.lookupExpression? terminal.expression = some node := by
    simpa only [sourceEq] using found
  have childTyped : ExpressionHasType child.source header.context terminal.expression node.type := by
    simpa only [sourceEq] using typed
  have childProfile : MethodStepPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt directSites := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have noCalls : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect
      (compiled := compiled) (invocation := child) certificate :=
    CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect.of_source certificate
      (by simpa only [sourceEq] using noIndirect)
  let support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages) header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults :=
    CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt.ofRoot {
      compilerFuel := fuel + 1
      accepted := accepted
      certificate := certificate
      node := node
      found := childFound
      rawResult := rawType
      typed := childTyped
      sameLedger := header.valid.ledger.trans terminal.aligned.solved
      runtimeLedger := RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed
      unique := unique
      wellFormed := wellFormed
      runtime := runtime
      covers := by
        rw [(RecursiveNamedPreparedStageScopes.registry actualStages).evidence selected]
        exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
      actualFunctionType := by rw [root.callables]; rfl
      uninitialized := fun _ _ _ read _ location =>
        CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
          terminal.aligned receiver (by simpa only [sourceEq] using read) location
      callsReady := by intro callFuel callScope id callee ids metadata lowered compiler path; exact False.elim (noCalls compiler path)
      directReady := direct_ready terminal wellFormed metadata tree rows covered root sourceEq selected certificate
      indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
        terminal.prepared diagnostic terminal.aligned sourceEq certificate
      methodReady := method_ready_generic terminal wellFormed metadata tree checked catalog methods actualStages root sourceEq selected certificate
      noIndirect := noCalls }
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
/-- Original named compilation, real caller evidence and the actual method cache
produce the physical body support. Every execution premise comes later. -/
theorem of_actual_generic
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  obtain ⟨fuel, ⟨root⟩⟩ := policy_receipt terminal
  exact ⟨⟨point, fun child selected => at_scope_sites_generic terminal diagnostic receiver wellFormed supported metadata tree
    rows covered noIndirect checked catalog methods actualStages root child selected⟩⟩

end Generic

section Legacy
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include wellFormed metadata tree checked catalog methods actualStages in
theorem method_ready {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  exact method_ready_generic terminal wellFormed metadata tree checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root sameSource selected certificate

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root child selected

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
theorem of_actual
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages point

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
