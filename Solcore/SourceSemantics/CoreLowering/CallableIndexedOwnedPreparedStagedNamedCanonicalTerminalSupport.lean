import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedScopeCoherence

/-! A named terminal's original compiler policy produces finite recursive
expression support. Actual Source typing, diagnostic issuance and selected
sidecars supply the call ports; no execution or payload representation is an
input. The original contextual callback keeps its own compiler budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (MetadataFor NativeMetadataFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

/-- The accepted terminal callback selects its actual complete policy. -/
theorem policy_receipt :
    ∃ fuel, Nonempty (RootPolicyReceipt (compiled := compiled)
      terminal.prepared.named terminal.prepared.diagnostics terminal.prepared.code
      terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child) := by
  have accepted := terminal.receipt.generated
  rw [CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.expression_callback terminal] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext terminal.prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    terminal.prepared.compilation.parents terminal.prepared.compilation.own.assignments terminal.prepared.diagnostics
    (context compiled.indexed terminal.prepared.named) compiled.indexed.base.callableContext none none
    terminal.receipt.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression header.reasonAt = .ok terminal.receipt.child at accepted
  have nonzero := CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.child_fuel_positive terminal
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      terminal.prepared.named.signature.key = .ok terminal.prepared.named.specialized := by
    simpa only [terminal.aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  exact ⟨fuel, RootPolicyReceipt.of_accepted terminal.prepared.compilation record
    (by simpa only [fuelEq] using accepted)⟩

/-- A selected invocation's authority retains its original prepared sidecar.
The Source view and guard frame are static consequences of registry selection. -/
structure SidecarAt (invocation : Staging.Recursive.Scope) where
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
    terminal.prepared.named.signature.key = .ok sidecar
  view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source header.function.source
  guards : invocation.guards = CallableLedger.frame sidecar

/-- Read the actual sidecar result once; the existence receipt supplies only
its proof fields. This is constructive and does not choose a runtime witness. -/
def SidecarAt.of_exists {invocation : Staging.Recursive.Scope}
    (observed : ∃ sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        terminal.prepared.named.signature.key = .ok sidecar ∧
      CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source header.function.source ∧
      invocation.guards = CallableLedger.frame sidecar) : SidecarAt terminal invocation := by
  cases issued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      terminal.prepared.named.signature.key with
  | error error =>
    exact False.elim (by
      obtain ⟨sidecar, accepted, _⟩ := observed
      rw [issued] at accepted
      cases accepted)
  | ok sidecar =>
    refine ⟨sidecar, issued, ?_, ?_⟩
    all_goals
      obtain ⟨actual, accepted, view, guards⟩ := observed
      have same := Except.ok.inj (issued.symm.trans accepted)
      subst actual
      assumption

private theorem original_unique {original actual : TypedSource}
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView original actual)
    (unique : NodeOccurrencesUnique actual) : NodeOccurrencesUnique original := by
  rcases view with same | ⟨active, same⟩
  · exact same ▸ unique
  · rw [same] at unique
    change ((original.applySubstitution active).nodes.map Node.occurrenceId).Nodup at unique
    change (original.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (metadata : NativeMetadataFor compiled.indexed terminal.prepared.named header.function.source)
  (tree : GeneralSyntax header.function.source terminal.expression)
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

include metadata in
/-- Every reached indirect call uses the same root policy and real sidecar.
The original parent typing supplies the callee occurrence and raw types. -/
theorem calls_ready {fuel : Nat}
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
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax path
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.recipe_policy_for_native
    root.compilerPolicy metadata callScope header.reasonAt
  have readPolicy := profile.read id (by simpa only [sameSource] using syntaxTree)
  have childRead : root.selected.policy.readExpression invocation.source id =
      SourceCoreCompatibleDataExpressions.readExpression
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source id := by
    simpa only [sameSource] using readPolicy
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

include diagnostic receiver wellFormed metadata tree rows complete in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope {fuel : Nat}
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
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.recipe_policy_for_native
    root.compilerPolicy metadata (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
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
  have childProfile : GeneralPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, GeneralSyntax child.source id →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : GeneralSyntax child.source terminal.expression := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    calls_ready terminal metadata root sourceEq authority childTyped certificate
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  let support := CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.of_general_compiled
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted ready rawType
    (header.valid.ledger.trans terminal.aligned.solved)
    (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed)
    wellFormed runtime
    (by rw [stages.evidence selected]; exact RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
        terminal.aligned receiver (by simpa only [sourceEq] using receipt) location) rows complete rfl rfl
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed metadata tree rows complete zero in
/-- Genuine root acceptance produces the finite certificate at every actual
selected scope. The returned support feeds the existing public body family. -/
theorem of_terminal_native
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
  exact at_scope terminal diagnostic receiver wellFormed metadata tree rows complete root child selected (scopes child selected)

include diagnostic receiver wellFormed metadata tree rows complete zero in
/-- The actual named hook supplies its canonical sidecar. Genuine Source
origins and program typing identify every selected guard frame, without
excluding lambdas or other specializations of the same declaration. -/
theorem of_actual_native
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
  apply of_terminal_native terminal diagnostic receiver wellFormed metadata tree rows complete zero point
  intro child selected
  refine { sidecar := sidecar, issued := ?_, view := .inl canonicalSource, guards := ?_ }
  · simpa only [terminal.aligned.named] using issued
  · exact RecursiveNamedPreparedScopeCoherence.selected_frame actual
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected

include diagnostic receiver wellFormed in
/-- Ordinary metadata remains a direct specialization of the native-literal
issuer; existing callers keep their original public support signature. -/
theorem of_terminal
    (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source)
    (tree : GeneralSyntax header.function.source terminal.expression)
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (scopes : ∀ child, stages.Closure header.function child → SidecarAt terminal child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys)
      stages faults header terminal) :=
  of_terminal_native terminal diagnostic receiver wellFormed (NativeMetadataFor.of_ordinary metadata)
    tree rows complete zero point scopes

include diagnostic receiver wellFormed in
/-- The ordinary actual-root producer is preserved without discarding genuine
native literal evidence from the more general accepted compiler path. -/
theorem of_actual
    (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source)
    (tree : GeneralSyntax header.function.source terminal.expression)
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys)
      (RecursiveNamedPreparedStageScopes.registry actual) faults header terminal) :=
  of_actual_native terminal diagnostic receiver wellFormed (NativeMetadataFor.of_ordinary metadata)
    tree rows complete zero actual point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
