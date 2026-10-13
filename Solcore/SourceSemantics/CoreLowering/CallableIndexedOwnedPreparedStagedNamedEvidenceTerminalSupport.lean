import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles

/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (StepPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
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

section Sites
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
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)

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
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy
    root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
  have readPolicy := profile
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

include wellFormed metadata tree rows complete in
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
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete rfl rfl
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by
    simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
  have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
  rcases CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.accepted_direct_action
    root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
  · obtain ⟨requirements, assumptions⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
        compiler.metadata.found compiler.form bypass
    have special := fun callback budget =>
      (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.direct_hook root.compilerPolicy
        childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
        (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
          compiler.metadata.coercions assumptions)
    have ordinary := compiler.ordinary special
      (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy root.compilerPolicy childMetadata actualTree)
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements header.context child.evidence⟩⟩
  · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
      compiler.metadata.found compiler.form authentic
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
      compiler port actual caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩

include diagnostic receiver wellFormed supported metadata tree rows complete in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  have sourceEq := stages.source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.recipe_policy_for
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
  have childProfile : StepPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
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
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    calls_ready_sites terminal metadata tree root sourceEq authority childTyped certificate
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  let support := CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.of_steps_compiled
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted ready rawType
    (header.valid.ledger.trans terminal.aligned.solved)
    (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed)
    wellFormed runtime
    (by rw [stages.evidence selected]; exact RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
        terminal.aligned receiver (by simpa only [sourceEq] using receipt) location) rows
    (direct_ready terminal wellFormed metadata tree rows complete root sourceEq selected certificate)
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      terminal.prepared diagnostic terminal.aligned sourceEq certificate)
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows complete zero in
/-- Genuine root acceptance produces the finite certificate at every actual
selected scope. The returned support feeds the existing public body family. -/
theorem of_terminal
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (scopes : ∀ child, stages.Closure header.function child → SidecarAt terminal child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys) stages faults header terminal) := by
  obtain ⟨fuel, root⟩ := policy_receipt terminal
  obtain ⟨root⟩ := root
  refine ⟨{ point := point, zero := zero, roots := ?_ }⟩
  intro child selected
  exact at_scope_sites terminal diagnostic receiver wellFormed supported metadata tree rows complete root child selected (scopes child selected)

include diagnostic receiver wellFormed supported metadata tree rows complete zero in
/-- The actual named hook supplies its canonical sidecar. Genuine Source
origins and program typing identify every selected guard frame, without
excluding lambdas or other specializations of the same declaration. -/
theorem of_actual
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys)
      (RecursiveNamedPreparedStageScopes.registry actual) faults header terminal) := by
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _genericMember, _requested, accepted⟩ :=
    terminal.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, terminal.aligned.named, terminal.prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  apply of_terminal terminal diagnostic receiver wellFormed supported metadata tree rows complete zero point
  intro child selected
  refine { sidecar := sidecar, issued := ?_, view := .inl canonicalSource, guards := ?_ }
  · simpa only [terminal.aligned.named] using issued
  · exact RecursiveNamedPreparedScopeCoherence.selected_frame actual
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected

end Sites

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport
