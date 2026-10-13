import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
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

private theorem original_unique {original actual : TypedSource}
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView original actual)
    (unique : NodeOccurrencesUnique actual) : NodeOccurrencesUnique original := by
  rcases view with same | ⟨active, same⟩
  · exact same ▸ unique
  · rw [same] at unique
    change ((original.applySubstitution active).nodes.map Node.occurrenceId).Nodup at unique
    change (original.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique

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
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include metadata tree in
/-- Every reached indirect call uses the same root policy and real sidecar.
The original parent typing supplies the callee occurrence and raw types. -/
theorem calls_ready_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {invocation : Staging.Recursive.Scope}
    (sameSource : invocation.source = header.function.source)
    (authority : SidecarAt terminal invocation)
    {type : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source header.context terminal.expression type)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) invocation.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
  intro callFuel callScope id callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path
    (by simpa only [sameSource] using tree)
  have readPolicy := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy
    root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
  have childRead : root.selected.policy.readExpression invocation.source id =
      SourceCoreCompatibleDataExpressions.readExpression
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source id := by
    simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler childRead
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler childRead [] root.callables
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨parameter, result, types, calleeTyped, _⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique parentTyped
  obtain ⟨node, contains, _⟩ := calleeTyped.stored_type
  exact ⟨{
    prepared := prepared
    sidecar := authority.sidecar
    caller := by rw [prepared.caller]; exact authority.issued
    view := by simpa only [sameSource] using authority.view
    guardFrame := authority.guards
    originalUnique := original_unique authority.view header.unique
    sourceParent := parent
    calleeNode := node
    calleeFound := lookupExpression?_complete unique contains }⟩


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites_with_catalog {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
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
  let support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages) header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults :=
    CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofRoot {
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
      callsReady := calls_ready_sites terminal metadata tree root sourceEq authority childTyped certificate
      directReady := CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.direct_ready terminal wellFormed metadata tree rows covered root sourceEq selected certificate
      indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
        terminal.prepared diagnostic terminal.aligned sourceEq certificate
      methodReady := CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.method_ready_with_catalog terminal wellFormed metadata tree checked catalog methods actualStages root sourceEq selected certificate }
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
/-- Original named compilation, real caller evidence and the actual method cache
produce the physical body support. Every execution premise comes later. -/
theorem of_actual_with_catalog
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  obtain ⟨fuel, ⟨root⟩⟩ := policy_receipt terminal
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _with_catalogMember, _requested, accepted⟩ :=
    terminal.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, terminal.aligned.named, terminal.prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  let authority : SidecarAt terminal child := {
    sidecar := sidecar
    issued := by simpa only [terminal.aligned.named] using issued
    view := .inl canonicalSource
    guards := RecursiveNamedPreparedScopeCoherence.selected_frame actualStages
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected }
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree
    rows covered checked catalog methods actualStages root child selected authority

end Generic


section GenericWrappers
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
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual_generic
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages point

end GenericWrappers

section EvidenceWrappers
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
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites_with_evidence {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual_with_evidence
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages point

end EvidenceWrappers

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
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages point

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
