import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation

/-!
# Staged bounds: selected body compiler

Compiler callbacks, certificates and factories of selected bodies, and recursive body and terminal caller bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
/-! A named terminal body retains either the existing recursive expression
certificate or the exact ordinary lambda producer. The latter keeps its static
body support and needs the genuine zero-prefix inventory; dynamic captures
are obtained later from the actual parameter packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
  (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
  (bodyRegistry : SourceCoreRawMetadata.Registry)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (stages : Staging.Recursive.Registry) (terminal : Terminal header)
  (semanticFaults : FunctionCalls.FaultRep)

structure Formation where
  point : terminal.certificate = Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    terminal.expression terminal.receipt.child
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  actual : ∀ child, stages.Closure header.function child →
    Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      header header.context child.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)

/-- One actual compiler occurrence suffices for every selected invocation:
selection preserves its evidence, and no runtime capture is supplied here. -/
theorem Formation.of_actual
    (point : terminal.certificate = Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
    (actual : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Formation headers keys bodyRegistry header stages terminal semanticFaults where
  point := point
  complete := complete
  zero := zero
  actual child selected := by
    rw [stages.evidence selected]
    exact ⟨actual⟩
  wellFormed := wellFormed

inductive LegacySupport where
  | recursive (static : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header stages terminal semanticFaults)
  | formation (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)

inductive Support where
  | recursive (static : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header stages terminal semanticFaults)
  | formation (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
  | canonical (static : CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := headers) (keys := keys) stages semanticFaults header terminal)

variable {headers keys bodyRegistry header stages terminal semanticFaults}
  {receiving : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem original_source {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    child.source = CallableIndexedNamedGeneration.source header.named := by
  rw [stages.source selected]
  exact header.agreement.source

private theorem Formation.runtime
    (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source := by
  obtain ⟨facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header static.wellFormed
  have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  rw [stages.source selected]
  exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)

private theorem Formation.covers
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) :
    child.evidence.Covers header.context := by
  rw [stages.evidence selected]
  exact RecursiveNamedInitialContextValidity.covers header.frame header.extended

/-- The static lambda alternative closes the same named-child preservation
interface; the actual invocation still supplies the packet and capture state. -/
theorem Formation.preserves (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow
      (headers := headers) (keys := keys) header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size _smaller current id lowered certified
  rw [static.point] at certified
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.preserves
    header owner header.context child profile static.complete terminal.aligned.globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (static.zero owner)
    (original_source selected) (by rw [stages.source selected]; exact header.unique)
    static.wellFormed (static.runtime selected) (Formation.covers selected) faults size
    (static.actual child selected)

/-- Native formation produces its independent Source grade and the full
reached-state result of the current named body interface. -/
theorem Formation.reflects (static : Formation headers keys bodyRegistry header stages terminal semanticFaults)
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child terminal.certificate faults budget := by
  refine .nested terminal.aligned.globals static.zero ?_
  intro owner size _smaller current id lowered certified
  rw [static.point] at certified
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.reflects
    header owner header.context child profile static.complete terminal.aligned.globals
    (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (static.zero owner)
    (original_source selected)
    static.wellFormed (static.runtime selected) (Formation.covers selected) faults size
    (static.actual child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
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

section Sites
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (ordinary : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compiled.indexed.base.plan instantiation)
  (metadata : NativeMetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
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

include diagnostic receiver wellFormed ordinary metadata tree rows complete in
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
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
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
  let support := CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.of_sites_compiled ordinary
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
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      terminal.prepared diagnostic terminal.aligned sourceEq certificate)
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed ordinary metadata tree rows complete zero in
/-- Genuine root acceptance produces the finite certificate at every actual
selected scope. The returned support feeds the existing public body family. -/
theorem of_terminal_native_sites
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
  exact at_scope_sites terminal diagnostic receiver wellFormed ordinary metadata tree rows complete root child selected (scopes child selected)

include diagnostic receiver wellFormed ordinary metadata tree rows complete zero in
/-- The actual named hook supplies its canonical sidecar. Genuine Source
origins and program typing identify every selected guard frame, without
excluding lambdas or other specializations of the same declaration. -/
theorem of_actual_native_sites
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
  apply of_terminal_native_sites terminal diagnostic receiver wellFormed ordinary metadata tree rows complete zero point
  intro child selected
  refine { sidecar := sidecar, issued := ?_, view := .inl canonicalSource, guards := ?_ }
  · simpa only [terminal.aligned.named] using issued
  · exact RecursiveNamedPreparedScopeCoherence.selected_frame actual
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected

end Sites

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

include diagnostic receiver wellFormed metadata tree rows complete zero in
theorem of_terminal_native
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (scopes : ∀ child, stages.Closure header.function child → SidecarAt terminal child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys) stages faults header terminal) := by
  exact of_terminal_native_sites terminal diagnostic receiver wellFormed
    (fun _ supported => supported.ordinary compiled.indexed.base.plan) metadata tree rows complete zero point scopes

include diagnostic receiver wellFormed metadata tree rows complete zero in
theorem of_actual_native
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys)
      (RecursiveNamedPreparedStageScopes.registry actual) faults header terminal) := by
  exact of_actual_native_sites terminal diagnostic receiver wellFormed
    (fun _ supported => supported.ordinary compiled.indexed.base.plan) metadata tree rows complete zero actual point

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
/-! Static restriction to the terminal compiler's actual used child.
The closure restriction reuses the checked same-Code used-child producers.
The new named restriction uses its accepted action to expose a single point.
These producers contain no execution, body meaning or runtime state.
Original Source compiler authority remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (code : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point scope id code

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {stages : Staging.Recursive.Registry}

/-- Keep the same Code/selected scope and narrow only its child certificate. -/
def closure {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow (code := code) terminal

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Specialize the restriction through the actual ordinary/principal Code. -/
def closureFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrowFor association terminal

/-- Keep this Header's actual receipt/alignment and expose its unique used child. -/
def named (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header) :
    CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header :=
  { terminal with
    certificate := Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child
    certifies := by
      intro lowered accepted
      exact ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans terminal.receipt.generated)⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
/-! The real contextual lambda producer retains its body recipe before the
ordinary Site forgets it. The compatible representation's loop policy then
supplies the expression callback and statement reader by construction. Its
actual lambda body receipt supplies terminal acceptance. There is no callback
equality, original body acceptance, or execution law in the public producer's
inputs. Raw Source typing, original policy coverage and reached-call authority
remain separate at the original selected parameter context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration

/-- The concrete marked representation preserves the supplied expression
callback through its allocator and ancestry updates. -/
def loop_policy {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) : SourceCoreLoops.Policy :=
  let actual := (representation prepared).atContext named.signature.key []
  { actual.loopsWithSourceCells actual.expressions.sourceCells
      (context prepared named).solvedRequirements assignments diagnostics
      (context prepared named).owner expression with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder
      actual prepared.base.locals named.signature.key [] }

theorem expression_callback {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    (loop_policy prepared named assignments diagnostics expression).lowerExpression = expression := by
  rfl

theorem statement_reader {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    (loop_policy prepared named assignments diagnostics expression).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement checked := by
  rfl

/-- The actual production body lowerer uses that same concrete loop policy. -/
theorem body_lowerer {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    SourceCoreGeneralFunctions.bodyLowererWithRepresentation
      ((representation prepared).atContext named.signature.key [])
      (context prepared named).solvedRequirements assignments diagnostics
      (context prepared named).owner
      (SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key [])
        prepared.base.locals named.signature.key []) expression =
      SourceCoreLoops.lowerStatementsWithPolicy
        (loop_policy prepared named assignments diagnostics expression) := by
  rfl

/-- The retained body recipe belongs to the same chosen compiler Site. This
is a static compiler packet, not a called-body meaning certificate. -/
structure Produced (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : Named) (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : CallableIndexedLambdaGeneration.Site compiled.indexed named parameters result statements
    sourceContext evidence captured scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binder : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key []
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code
  callback : site.code.lowerBody
      (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy
      (loop_policy compiled.indexed named compilation.own.assignments diagnostics
        (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))

/-- Run the checked original contextual producer once and keep its exact body
recipe. In particular, the callback field is constructed from compiler success. -/
theorem of_contextual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (Produced compiled named diagnostics namedCode compilation parameters result statements
      sourceContext evidence captured scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binder, recipe, issuedRecipe, _view, _reason⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact compiled.indexed
      compilation issued record sourceContext evidence captured profile viewOfSource sourceFound sourceForm
      found form owner requirements coercions ordinary read accepted typed
  refine ⟨{
    site := site
    identifier := identifier
    emitted := emitted
    binder := binder
    recipe := recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe
    callback := ?_ }⟩
  have applied := congrArg
    (fun body : SourceCoreFunctions.BodyLowerer =>
      body (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))
    recipe
  exact applied.trans (body_lowerer compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))

section Terminal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {captured : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced compiled named diagnostics namedCode compilation parameters result statements
    sourceContext evidence captured scope administrative id lowered)

/-- The production callback and real body receipt construct the terminal
packet directly. No arbitrary BodyWith policy is replaced or inferred. -/
theorem terminal {stages : Staging.Recursive.Registry} (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      produced.site.code.view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (CallableIndexedLambdaGeneration.closure named parameters result statements
        sourceContext evidence captured) child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
        produced.site.code stages,
      packet.policy.lowerExpression = FunctionCode.children produced.site.code.policy
        produced.site.code.lowerBody produced.site.code.fuel produced.site.code.compilation ∧
      packet.reasonAt = produced.site.code.reasonAt ∧ packet.child = child ∧
      packet.expression = expression ∧
      packet.certificate = CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
        (produced.site.code.receipt.loweredParameters.reverse.map
          (fun binding => (binding.1.id, binding.2)) ++ scope) expression packet.receipt.child := by
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
      produced.site.code.fuel produced.site.code.compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    produced.site.code policy produced.callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (statement_reader compiled.indexed named compilation.own.assignments diagnostics
      (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
        produced.site.code.fuel produced.site.code.compilation)) shape accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
      produced.site.code stages := {
    policy := policy
    fuel := produced.site.code.fuel
    expression := expression
    reasonAt := produced.site.code.reasonAt
    fellThrough := produced.site.code.compilation.internalReason
    escaped := produced.site.code.compilation.internalReason
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
      (produced.site.code.receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) expression receipt.child
    certifies := by
      intro actual generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  exact ⟨packet, expression_callback compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
      produced.site.code.fuel produced.site.code.compilation), rfl, rfl, rfl, rfl⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
/-! Numeric recursion supplies the selected called bodies internally. The
  carrier is the concrete owned pool at universe zero. Each recursive use
  consumes an authentic original Source Root at a strictly smaller grade;
  structural caller recursion handles equal native grades for groups and
  singleton tuples. Static support stores no execution or semantic callback.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt SelectedBody NamedSupport ClosureSupportFor)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- The IH ranges over the exact original Source, parameter context and
  compiler child. All states, stores, mappings and renamings stay quantified
  inside the admitted expression law. -/
def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered},
    RootAt compiled context invocation scope expression lowered semanticFaults →
    PreservesAt poolBridge context model stages invocation
      (Point scope expression lowered) callFaults size

/-- Reflection retains its independent Source grade and exact failure scope. -/
def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered},
    RootAt compiled context invocation scope expression lowered semanticFaults →
    ReflectsAt poolBridge context model stages invocation
      (Point scope expression lowered) callFaults size

variable {profile}

theorem selected_body_preserves_below
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    (support : SelectedBody code inputs stages packet semanticFaults)
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget) :
    ∀ child : Staging.Recursive.Scope, stages.Closure function child →
      PreservesBelow poolBridge inputs.context model stages child packet.certificate callFaults size := by
  intro child selected childSize smaller current id lowered point
  rw [support.point] at point
  exact children childSize (Nat.lt_of_lt_of_le smaller within)
    (support.rootAt child selected) point

theorem selected_body_reflects_below
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    (support : SelectedBody code inputs stages packet semanticFaults)
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget) :
    ReflectsBelow poolBridge inputs.context model stages packet.child packet.certificate callFaults size := by
  intro childSize smaller current id lowered point
  rw [support.point] at point
  exact children childSize (Nat.lt_of_lt_of_le smaller within)
    (support.rootAt packet.child packet.selected) point

variable
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

include closureSupport in
theorem closure_preserves_below
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
      association (closureTerminals association) functions size := by
  have supported := closureSupport association
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body_preserves_below supported children within
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body_preserves_below supported children within

include closureSupport in
theorem closure_reflects_below
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
      association (closureTerminals association) functions size := by
  have supported := closureSupport association
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body_reflects_below supported children within
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body_reflects_below supported children within

include namedSupport in
theorem named_preserves_below
    {budget : Nat} (children : ∀ size, size < budget →
      PreservesRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
      header model stages child
      (namedTerminals header member).certificate callFaults size := by
  cases namedSupport header member with
  | recursive static =>
    apply CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow.pool
    intro childSize smaller current id lowered point
    rw [static.point] at point
    exact children childSize (Nat.lt_of_lt_of_le smaller within)
      (static.roots child selected).val point
  | formation static =>
    exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.preserves
      (profile := profile) (faults := callFaults) static selected size

include namedSupport in
theorem named_reflects_below
    {budget : Nat} (children : ∀ size, size < budget →
      ReflectsRootsAt (completion := completion) (stages := stages)
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size)
    {size : Nat} (within : size ≤ budget)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
      header model stages child
      (namedTerminals header member).certificate callFaults size := by
  cases namedSupport header member with
  | recursive static =>
    apply CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow.pool
    intro childSize smaller current id lowered point
    rw [static.point] at point
    exact children childSize (Nat.lt_of_lt_of_le smaller within)
      (static.roots child selected).val point
  | formation static =>
    exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.reflects
      (profile := profile) (faults := callFaults) static selected size

variable
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- This family constructs every recursive called-body preservation law.
  Only static original compiler authority and chosen terminal support enter. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages)
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.preserves_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closureTerminals namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize within => closure_preserves_below closureTerminals closureSupport ih within)
        (fun childSize within => named_preserves_below namedTerminals namedSupport ih within)
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _)

include receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Native grades decrease through called bodies. The structural fold handles
  equal-grade native group and singleton tuple children without changing the
  independent Source grade returned by reflection. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages)
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.reflects_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closureTerminals namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize within => closure_reflects_below closureTerminals closureSupport ih within)
        (fun childSize within => named_reflects_below namedTerminals namedSupport ih within)
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
/-! An arbitrary admitted caller consumes the closed concrete pool body
  family. Its protocol carrier remains independent of the pool's universe;
  the existing call producers restore its actual reached state around the
  literal returned pool. Every child expression and called-body semantic law
  is constructed internally from static original Source authority.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Source traces retain every reached caller effect and their original
  admission receipt while recursive body meaning is supplied internally. -/
theorem preserves {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point scope expression lowered) callFaults size := by
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.preserves
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) (closureTerminals := closureTerminals)
      (namedTerminals := namedTerminals) (closureSupport := closureSupport) (namedSupport := namedSupport)
  intro current id child point
  exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.preserves_reached
    bridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
    root.support.covers root.support.unique root.support.actualFunctionType observations
    extension semantic closureTerminals namedTerminals root.support.sameLedger
    root.support.runtimeLedger root.support.uninitialized size
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.closure_preserves_below
      closureTerminals closureSupport (fun smaller _ => bodies smaller) within)
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_preserves_below
      namedTerminals namedSupport (fun smaller _ => bodies smaller) within)
    root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _) point

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Native completion returns its authentic independently graded Source
  trace, exact nested failure scope and restored caller relation and post. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point scope expression lowered) callFaults size := by
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.reflects
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) (closureTerminals := closureTerminals)
      (namedTerminals := namedTerminals) (closureSupport := closureSupport) (namedSupport := namedSupport) stageEq
  intro current id child point
  exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.reflects_reached
    bridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
    root.support.covers root.support.unique root.support.actualFunctionType observations
    extension semantic closureTerminals namedTerminals root.support.sameLedger
    root.support.runtimeLedger root.support.uninitialized stageEq size
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.closure_reflects_below
      closureTerminals closureSupport (fun smaller _ => bodies smaller) within)
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_reflects_below
      namedTerminals namedSupport (fun smaller _ => bodies smaller) within)
    root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _) point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
/-! Static selected-body support is built at the actual original parameter
context. Original frame typing supplies the child node and raw result type;
the compiler-root issuer constructs acceptance and the recursive certificate.
Every actual Source-selected scope is retained. Remaining declaration,
coercion, policy, diagnostic, runtime and reached-call authority is explicit.
No expression execution or called-body meaning is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt SelectedBody NamedSupport ClosureSupportFor)


/-- Original static conditions omit child lookup and typing: the actual frame
or Header supplies those independently of the native projection. -/
structure OriginalConditions (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (semanticFaults : FunctionCalls.FaultRep) where
  declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context
  coercions : ∀ id node, Syntax invocation.source id →
    invocation.source.lookupExpression? id = some node → node.coercions = []
  sameLedger : context.solvedRequirements = compilation.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source
  covers : invocation.evidence.Covers context
  actualFunctionType : policy.callables.functionType = CallableContract.functionType
  uninitialized : ∀ current id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)

structure OriginalConditionsOn (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (roots : List NodeId) (semanticFaults : FunctionCalls.FaultRep) where
  declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context
  coercions : ∀ id node, Syntax invocation.source id →
    invocation.source.lookupExpression? id = some node → node.coercions = []
  sameLedger : context.solvedRequirements = compilation.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source
  covers : invocation.evidence.Covers context
  actualFunctionType : policy.callables.functionType = CallableContract.functionType
  uninitialized : ∀ current id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current id lowered →
    Reaches invocation.source roots (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)

/-- Global static authority restricts to any actual body root set. -/
theorem OriginalConditions.on
    {compiled : SourceCoreUnifiedCompilation.Compiled} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {invocation : Staging.Recursive.Scope} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    (conditions : OriginalConditions compiled policy compilation readFuel context invocation
      reasonAt scope semanticFaults) (roots : List NodeId) :
    OriginalConditionsOn compiled policy compilation readFuel context invocation
      reasonAt scope roots semanticFaults where
  declarations := conditions.declarations
  coercions := conditions.coercions
  sameLedger := conditions.sameLedger
  runtimeLedger := conditions.runtimeLedger
  unique := conditions.unique
  wellFormed := conditions.wellFormed
  runtime := conditions.runtime
  covers := conditions.covers
  actualFunctionType := conditions.actualFunctionType
  uninitialized := fun current id lowered receipt _reached =>
    conditions.uninitialized current id lowered receipt

/-- The actual Source lookup supplies its own node. Raw typing proves that
lookup succeeds; no choice of an execution, compiler action or node is needed. -/
def original_authority
    {compiled : SourceCoreUnifiedCompilation.Compiled} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {invocation : Staging.Recursive.Scope} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {rawType : TypeSystem.Ty}
    {semanticFaults : FunctionCalls.FaultRep}
    (conditions : OriginalConditions compiled policy compilation readFuel context invocation
      reasonAt scope semanticFaults)
    (raw : ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = rawType ∧ ExpressionHasType invocation.source context expression node.type) :
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.OriginalAuthority compiled policy compilation readFuel context invocation
      reasonAt scope expression rawType semanticFaults := by
  have available : (invocation.source.lookupExpression? expression).isSome := by
    obtain ⟨original, originalFound, _⟩ := raw
    exact Option.isSome_of_eq_some originalFound
  let node := (invocation.source.lookupExpression? expression).get available
  have found : invocation.source.lookupExpression? expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = rawType ∧
      ExpressionHasType invocation.source context expression node.type := by
    obtain ⟨original, originalFound, properties⟩ := raw
    have same : original = node := Option.some.inj (originalFound.symm.trans found)
    simpa only [same] using properties
  exact {
    node := node
    found := found
    rawResult := properties.1
    typed := properties.2
    declarations := conditions.declarations
    coercions := conditions.coercions
    sameLedger := conditions.sameLedger
    runtimeLedger := conditions.runtimeLedger
    unique := conditions.unique
    wellFormed := conditions.wellFormed
    runtime := conditions.runtime
    covers := conditions.covers
    actualFunctionType := conditions.actualFunctionType
    uninitialized := fun current id lowered receipt _reached =>
      conditions.uninitialized current id lowered receipt }

/-- Read authority follows the actual child path within the same body. -/
def original_authority_on
    {compiled : SourceCoreUnifiedCompilation.Compiled} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {invocation : Staging.Recursive.Scope} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {rawType : TypeSystem.Ty}
    {semanticFaults : FunctionCalls.FaultRep}
    {roots : List NodeId}
    (conditions : OriginalConditionsOn compiled policy compilation readFuel context invocation
      reasonAt scope roots semanticFaults)
    (reached : Reaches invocation.source roots (.expression expression))
    (raw : ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = rawType ∧ ExpressionHasType invocation.source context expression node.type) :
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.OriginalAuthority compiled policy compilation readFuel context invocation
      reasonAt scope expression rawType semanticFaults := by
  have available : (invocation.source.lookupExpression? expression).isSome := by
    obtain ⟨original, originalFound, _⟩ := raw
    exact Option.isSome_of_eq_some originalFound
  let node := (invocation.source.lookupExpression? expression).get available
  have found : invocation.source.lookupExpression? expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = rawType ∧
      ExpressionHasType invocation.source context expression node.type := by
    obtain ⟨original, originalFound, properties⟩ := raw
    have same : original = node := Option.some.inj (originalFound.symm.trans found)
    simpa only [same] using properties
  exact {
    node := node
    found := found
    rawResult := properties.1
    typed := properties.2
    declarations := conditions.declarations
    coercions := conditions.coercions
    sameLedger := conditions.sameLedger
    runtimeLedger := conditions.runtimeLedger
    unique := conditions.unique
    wellFormed := conditions.wellFormed
    runtime := conditions.runtime
    covers := conditions.covers
    actualFunctionType := conditions.actualFunctionType
    uninitialized := fun current id lowered receipt path =>
      conditions.uninitialized current id lowered receipt (Reaches.from_root reached path) }

section Closure
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (code : Code compiled.indexed function localScope administrative)


/-- The accepted BodyWith builds the terminal packet directly. Its reason
function and chosen child are literal fields. The expression callback link
is a genuine additional factory condition, not a consequence of body.callback. -/
theorem terminal_of_actual_body
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {registry : SourceCoreRawMetadata.Registry}
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal code.view expression function.body)
    (reader : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (expressionCallback : body.policy.lowerExpression =
      FunctionCode.children code.policy code.lowerBody code.fuel code.compilation)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.policy.lowerExpression =
        FunctionCode.children code.policy code.lowerBody code.fuel code.compilation ∧
      packet.reasonAt = code.reasonAt ∧ packet.child = child ∧ packet.expression = expression ∧
      packet.certificate = CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) expression packet.receipt.child := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    reader shape body.accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
    { policy := body.policy
      fuel := code.fuel
      expression := expression
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      receipt := receipt
      certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) expression receipt.child
      certifies := by
        intro lowered accepted
        exact ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans receipt.generated)⟩
      child := child
      selected := selected }
  exact ⟨packet, expressionCallback, rfl, rfl, rfl, rfl⟩

/-- Static admission is provided for every actual Source-selected child.
The frame supplies original raw child typing at the same parameter entry. -/
structure ClosureAuthority
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure function child → LocalView child.source code.view changed
  avoids : ∀ child, stages.Closure function child →
    Avoids child.source (function.body.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure function child →
    PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) code.reasonAt
  viewProfile : PolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    code.view (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) code.reasonAt
  tree : Syntax code.view packet.expression
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  conditions : ∀ child, stages.Closure function child →
    OriginalConditions compiled code.policy code.compilation readFuel inputs.context child
      code.reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope) semanticFaults

variable {code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}

/-- This exact certificate is constructed from the accepted packet and raw
frame typing. Ready authority can refer only to its actual reachable calls. -/
theorem closure_certificate
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      code.policy code.lowerBody code.compilation authority.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source inputs.context code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate (authority.edited child selected) (authority.avoids child selected)
    (authority.sourceProfile child selected) authority.viewProfile code.callables authority.tree
    (by simpa only [stages.source selected] using CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
    (original_authority (authority.conditions child selected)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type code packet inputs authority.frame child selected))
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet authority.callback authority.reason)

def ClosureReady
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults)) : Prop :=
  ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure function child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) (closure_certificate authority child selected)

/-- The selected singleton and every original Root are built internally.
No universal arbitrary-terminal body law is required. -/
def selected_body
    (authority : ClosureAuthority code inputs packet (semanticFaults := semanticFaults))
    (ready : ClosureReady authority) :
    SelectedBody code inputs stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure code packet) semanticFaults where
  point := rfl
  readFuel := authority.readFuel
  roots := fun child selected =>
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_terminal code packet inputs child selected
      (authority.edited child selected) (authority.avoids child selected)
      (authority.sourceProfile child selected) authority.viewProfile authority.tree
      authority.callback authority.reason
      (original_authority (authority.conditions child selected)
        (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type code packet inputs authority.frame child selected))
      (ready child selected)).support
end Closure

section Associations
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  {stages : Staging.Recursive.Registry}

/-- Both branches retain their actual BodyWith.toContext, without a context cast. -/
def ClosureAuthorityFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Type :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      ClosureAuthority code support.body.toContext packet (semanticFaults := semanticFaults)
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      ClosureAuthority code support.body.toContext packet (semanticFaults := semanticFaults)

def ClosureReadyFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) :
    ClosureAuthorityFor association packet → Prop :=
  match association, packet with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _, _ => fun authority => ClosureReady authority
  | .principal _ _ _ _ _ _ _ _ _ _ _, _ => fun authority => ClosureReady authority

/-- The original contextual Association chooses the actual parameter context
and narrows only its retained terminal certificate. -/
def closure_support_for
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages)
    (authority : ClosureAuthorityFor association packet) (ready : ClosureReadyFor association packet authority) :
    ClosureSupportFor association stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor association packet) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals reference typed provenance =>
      exact selected_body authority ready
  | principal owner captured code history support origin globals leading reference typed provenance =>
      exact selected_body authority ready
end Associations

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)


/-- The Header's callback must be identified with its actual expression
compiler at this real budget. This static function link is not an accepted
action equation, and it is not derived from the closure BodyWith callback. -/
structure NamedAuthority where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  compilerFuel : Nat
  readFuel : Nat
  native : Option SourceCoreGeneralFunctions.CallableContext
  active : TypeSystem.Substitution
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  callback : header.policy.lowerExpression packet.receipt.childFuel header.function.source =
    SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation header.function.source
  profile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  tree : Syntax header.function.source packet.expression
  conditions : ∀ child, stages.Closure header.function child →
    OriginalConditions compiled policy compilation readFuel header.context child header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) semanticFaults

variable {header packet}

private theorem named_accepted
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    SourceCoreFunctions.lowerExpressionWithPolicy authority.policy authority.body authority.compilerFuel
      authority.compilation child.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) packet.expression header.reasonAt =
      .ok packet.receipt.child := by
  have callbackAt := congrArg
    (fun lower : SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
        Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr =>
      lower (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression header.reasonAt) authority.callback
  have generated := callbackAt.symm.trans packet.receipt.generated
  simpa only [stages.source selected] using generated

private theorem named_raw
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType child.source header.context packet.expression node.type := by
  have raw := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
    packet.receipt selected (authority.conditions child selected).wellFormed
  simpa only [stages.source selected] using raw

private theorem named_avoids (child : Staging.Recursive.Scope) :
    Avoids child.source [.expression packet.expression] [] := by
  intro id member
  cases member

/-- The selected Header's original callback generates this exact certificate.
Identity view transport here carries no changed expression metadata. -/
theorem named_certificate
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      authority.policy authority.body authority.compilation authority.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate (LocalView.refl child.source) (named_avoids (packet := packet) child)
    (by simpa only [stages.source selected] using authority.profile)
    (by simpa only [stages.source selected] using authority.profile)
    authority.callables (by simpa only [stages.source selected] using authority.tree)
    (.root (by simp))
    (original_authority (authority.conditions child selected) (named_raw authority child selected))
    (named_accepted authority child selected)

def NamedReady
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults)) : Prop :=
  ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child),
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) (named_certificate authority child selected)

/-- The original Source parameter context, raw result and reason function
remain this Header's fields, and all genuine selected child scopes are covered. -/
def named_support
    (authority : NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : NamedReady authority) :
    NamedSupport header stages (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named header packet) semanticFaults where
  point := rfl
  roots := by
    intro child selected
    simp only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named]
    exact ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action (LocalView.refl child.source) (named_avoids (packet := packet) child)
      (by simpa only [stages.source selected] using authority.profile)
      (by simpa only [stages.source selected] using authority.profile)
      authority.callables (by simpa only [stages.source selected] using authority.tree)
      (.root (by simp))
      (original_authority (authority.conditions child selected) (named_raw authority child selected))
      (named_accepted authority child selected) (ready child selected), rfl, rfl⟩
end Named

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
/-! A produced contextual lambda keeps its compiler recipe through recapture
and ordinary Association construction. The Code, static body and terminal
packet all belong to that same Site. No emitted-value equality identifies an
unrelated Code, and arbitrary existing Associations do not gain this receipt.
Original policy coverage and reachable-call authority remain separate static
conditions at the literal chosen packet and every selected Source scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (Produced loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
  (OriginalConditions ClosureAuthority ClosureReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}

section Seed
variable (produced : Produced compiled caller.named diagnostics namedCode compilation
  parameters result statements sourceContext evidence [] scope administrative id lowered)

/-- Recapture changes only the actual stored Source environment. -/
abbrev function (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named parameters result statements
    sourceContext evidence environment

def code (environment : Dynamic.Environment) :
    Code compiled.indexed (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) scope administrative :=
  RecursiveNamedLambdaFormationHeads.recaptureCode
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
    produced.site.code environment

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates
  produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

/-- The actual static body is recaptured beside the same compiler Site. -/
def ordinary_support (environment : Dynamic.Environment) :
    CallableIndexedOwnedOrdinaryLambdaSupport.Support
      (code produced environment) bodyRegistry semanticFaults :=
  (CallableIndexedOwnedOrdinaryLambdaSupport.Support.of_site
    caller produced.site expressionSyntax certificates body).recapture environment

variable (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
  (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)

include bodyView bodyReasons declarations in
/-- Source Syntax and the real binder policy remain original seed receipts. -/
theorem provenance
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context
      (.statements true statements) result)
    (environment : Dynamic.Environment)
    (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence) :
    OrdinaryAt (code produced environment) (ordinary_support produced body environment) :=
  .recaptured caller produced.site expressionSyntax certificates body produced.binder
    (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation produced.recipe)
    produced.compilerPolicy produced.issuedRecipe bodyView bodyReasons declarations syntaxTree environment callerGlobals callerReceipt

/-- The retained compiler recipe survives recapture without an equality cast
between different Codes or an assumption about a BodyWith expression callback. -/
theorem body_callback (environment : Dynamic.Environment) :
    (code produced environment).lowerBody
        (FunctionCode.children (code produced environment).policy
          (code produced environment).lowerBody (code produced environment).fuel
          (code produced environment).compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy
        (loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
          (FunctionCode.children (code produced environment).policy
            (code produced environment).lowerBody (code produced environment).fuel
            (code produced environment).compilation)) := by
  exact produced.callback

section Terminal
variable {stages : Staging.Recursive.Registry}

/-- The same production Code supplies the actual terminal compiler receipt. -/
theorem terminal (environment : Dynamic.Environment) (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      (code produced environment).view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
        (code produced environment) stages,
      packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
        (code produced environment).lowerBody (code produced environment).fuel
        (code produced environment).compilation ∧
      packet.reasonAt = (code produced environment).reasonAt ∧
      packet.expression = expression ∧ packet.child = child := by
  let policy := loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (code produced environment) policy (body_callback produced environment)
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation)) shape accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
      (code produced environment) stages := {
    policy := policy
    fuel := (code produced environment).fuel
    expression := expression
    reasonAt := (code produced environment).reasonAt
    fellThrough := (code produced environment).compilation.internalReason
    escaped := (code produced environment).compilation.internalReason
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) expression receipt.child
    certifies := by
      intro actual generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  exact ⟨packet, CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
    compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation), rfl, rfl, rfl⟩

/-- Choice retains the packet whose compiler callback was actually produced. -/
structure Choice (environment : Dynamic.Environment) (stages : Staging.Recursive.Registry) where
  packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
    (code produced environment) stages
  callback : packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
    (code produced environment).lowerBody (code produced environment).fuel
    (code produced environment).compilation
  reason : packet.reasonAt = (code produced environment).reasonAt
  requested : ExpressionId
  expression : packet.expression = requested
  child : Staging.Recursive.Scope
  sameChild : packet.child = child

theorem choose (environment : Dynamic.Environment) (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      (code produced environment).view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    Nonempty (Choice produced environment stages) := by
  obtain ⟨packet, callback, reason, expressionEq, childEq⟩ :=
    terminal produced environment expression shape child selected
  exact ⟨{
    packet := packet
    callback := callback
    reason := reason
    requested := expression
    expression := expressionEq
    child := child
    sameChild := childEq }⟩

variable {environment : Dynamic.Environment}
  (choice : Choice produced environment stages)

/-- The Source policy and raw context remain independent of compiler success.
The actual frame is already present in the retained same-Site static body. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    CallableLambdaViewEdits.LocalView child.source (code produced environment).view changed
  avoids : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    CallableLambdaBodyReachability.Avoids child.source (statements.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) (code produced environment).reasonAt
  viewProfile : PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (code produced environment).view
    ((code produced environment).receipt.loweredParameters.reverse.map
      (fun binding => (binding.1.id, binding.2)) ++ scope) (code produced environment).reasonAt
  tree : Syntax (code produced environment).view choice.packet.expression
  original : ∀ child, stages.Closure (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    OriginalConditions compiled (code produced environment).policy (code produced environment).compilation readFuel
      (ordinary_support produced body environment).body.toContext.context child (code produced environment).reasonAt
      ((code produced environment).receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) semanticFaults

def authority (conditions : Conditions produced body choice) :
    ClosureAuthority (code produced environment)
      (ordinary_support produced body environment).body.toContext choice.packet
      (semanticFaults := semanticFaults) := {
  frame := (ordinary_support produced body environment).body.frame
  readFuel := conditions.readFuel
  changed := conditions.changed
  edited := conditions.edited
  avoids := conditions.avoids
  sourceProfile := conditions.sourceProfile
  viewProfile := conditions.viewProfile
  tree := conditions.tree
  callback := choice.callback
  reason := choice.reason
  conditions := conditions.original }

def Ready (conditions : Conditions produced body choice) : Prop :=
  ClosureReady (authority produced body choice conditions)

def selected_body (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.SelectedBody
      (code produced environment) (ordinary_support produced body environment).body.toContext stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure
        (code produced environment) choice.packet) semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body
    (authority produced body choice conditions) ready
end Terminal
end Seed

section Association
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (produced : Produced compiled caller.named diagnostics namedCode compilation
    parameters result statements sourceContext evidence [] scope captured.administrative id lowered)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates
    produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

variable (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
  (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)

include bodyView bodyReasons declarations in
/-- The ordinary Association is constructed on the literal recaptured Code,
history and support. Its callback recipe remains available beside this object;
the usual runtime capture and formation fields are not reconstructed from a
native payload or its emitted expression. -/
def association
    (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence)
    (owner : OwnedKey keys) (history : CallableIndexedLambdaValues.History (code produced environment))
    (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
      (ordinary_support produced body environment) history)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) caller)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (referenceIndex : (code produced environment).referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value (code produced environment) captured.embedding history.native actual)
      (CallableContract.functionType (code produced environment).receipt.parameterCore
        (code produced environment).receipt.resultCore) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context (.statements true statements) result) :
    Association headers keys bodyRegistry semanticFaults mapping world
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
      (value (code produced environment) captured.embedding history.native actual)
      (code produced environment).receipt.loweredParameters
      (code produced environment).receipt.parameterCore (code produced environment).receipt.resultCore := by
  exact @Association.ordinary compiled headers keys bodyRegistry semanticFaults mapping world
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
    scope actual owner captured (code produced environment) history (ordinary_support produced body environment)
    origin prefixContext globals referenceIndex typed (provenance produced body bodyView bodyReasons declarations syntaxTree environment callerGlobals callerReceipt)

variable {stages : Staging.Recursive.Registry}
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence)
  (owner : OwnedKey keys) (history : CallableIndexedLambdaValues.History (code produced environment))
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
    (ordinary_support produced body environment) history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (referenceIndex : (code produced environment).referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (typed : RuntimeValueHasType world (value (code produced environment) captured.embedding history.native actual)
    (CallableContract.functionType (code produced environment).receipt.parameterCore
      (code produced environment).receipt.resultCore) compiled.indexed.layouts.definitions)
  (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
    (expressionSyntax (source caller.named)) body.context (.statements true statements) result)

/-- The authority belongs to the actual produced Association, not only a
closure with equal emitted payload. The Code and context reduce literally. -/
def authority_for (choice : Choice produced environment stages)
    (conditions : Conditions produced body choice) :
    CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthorityFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      choice.packet :=
  authority produced body choice conditions

/-- The usual checked support constructor retains this exact Association and
its chosen packet. Ready still concerns only its internally issued roots. -/
def support_for (choice : Choice produced environment stages)
    (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.ClosureSupportFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor
        (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
        choice.packet) :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.closure_support_for
    (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
    choice.packet
    (authority_for captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree choice conditions)
    ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCompilerTerminalCallerBounds
/-! Compiler terminal callers consume the constructive recursive body family.
Each chosen Association/Header packet is bundled with its original static
authority and the reachable-call authority of its exact issued certificate.
Selectors and body support are constructed internally from those bundles.
The public terminal endpoints issue their own original Root before invoking
the checked caller family; they accept no expression/body execution law.

Actual callback, policy, declaration, typing, diagnostic and CallsReady links
remain static inputs at the literal chosen packet and original caller scope.
Independent grades and full returned caller admission use the checked family.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCompilerTerminalCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt ClosureSupportFor NamedSupport)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

/-- One original contextual Association retains its actual Code and parameter
context. Ready refers only to certificates issued from this same packet. -/
structure ClosurePacket {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) where
  terminal : TerminalFor association stages
  authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthorityFor
    association terminal
  ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReadyFor
    association terminal authority

/-- A chosen Header retains its literal terminal receipt and original static
compiler conditions for every genuine Source-selected body scope. -/
structure NamedPacket
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  terminal : Terminal header
  authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
    header terminal (stages := stages) (semanticFaults := semanticFaults)
  ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority

/-- This is a static factory family, not a family of executions. It neither
equates Association contexts nor quantifies over arbitrary terminal certificates. -/
structure FactoryFamily where
  closures : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), ClosurePacket (stages := stages) association
  named : ∀ header, header ∈ headers →
    NamedPacket (stages := stages) (semanticFaults := semanticFaults) header

variable (factories : FactoryFamily (headers := headers) (keys := keys)
  (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (stages := stages))

/-- Only the certificate is narrowed. The chosen Code, receipt, child and
physical parameter scope remain those of the original Association packet. -/
def closure_terminals {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) : TerminalFor association stages :=
  CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor
    association (factories.closures association).terminal

/-- The same Header membership chooses the packet and all of its support. -/
def named_terminals
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) : Terminal header :=
  CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named
    header (factories.named header member).terminal

/-- Original raw typing and acceptance are manufactured by the authentic
factory at every selected body scope. No body meaning is stored in the bundle. -/
def closure_support {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    ClosureSupportFor association stages (closure_terminals factories association) :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.closure_support_for
    association (factories.closures association).terminal
    (factories.closures association).authority (factories.closures association).ready

/-- Named support uses the original Header source and the same chosen packet;
it does not infer an expression callback from the Header's statement policy. -/
def named_support
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) :
    NamedSupport header stages (named_terminals factories header member) semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support
    (factories.named header member).authority (factories.named header member).ready
end Static

section Meaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (factories : FactoryFamily (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (stages := stages))

include bridge receiver stagePrepared observations extension semantic factories in
private theorem preserves_issued {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults) (size : Nat) :
    PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages invocation (Point scope expression lowered)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closure_terminals factories) (namedTerminals := named_terminals factories)
    (closureSupport := closure_support factories) (namedSupport := fun header member => .recursive (named_support factories header member)) root size

include bridge receiver stagePrepared observations extension semantic factories in
private theorem reflects_issued
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults) (size : Nat) :
    ReflectsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages invocation (Point scope expression lowered)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closure_terminals factories) (namedTerminals := named_terminals factories)
    (closureSupport := closure_support factories) (namedSupport := fun header member => .recursive (named_support factories header member)) stageEq root size

section Closure
variable {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  {code : Code compiled.indexed function localScope administrative}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed) code}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}

include bridge receiver stagePrepared observations extension semantic factories in
/-- Frame typing, the actual terminal compiler action and original-source
transport construct this caller root internally at the literal parameter entry. -/
theorem preserves_closure
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthority
      code inputs packet (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) (size : Nat) :
    PreservesAt bridge inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body authority ready
  have root : RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure,
      CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow] using support.rootAt child selected
  intro current id lowered certified
  exact preserves_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    root size certified

include bridge receiver stagePrepared observations extension semantic factories in
/-- Reflection keeps its own native grade and authentic selected Source scope;
the independent Source grade and full returned post come from the checked family. -/
theorem reflects_closure
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthority
      code inputs packet (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) (size : Nat) :
    ReflectsAt bridge inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body authority ready
  have root : RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure,
      CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow] using support.rootAt child selected
  intro current id lowered certified
  exact reflects_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    stageEq root size certified
end Closure

section Named
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {packet : Terminal header}

include bridge receiver stagePrepared observations extension semantic factories in
/-- The actual Header source, ordered physical bindings and terminal receipt
issue the named root before recursive caller/body meaning is invoked. -/
theorem preserves_named
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
      header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) (size : Nat) :
    PreservesAt bridge header.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support authority ready
  have root : RootAt compiled header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named] using
      (support.roots child selected).val
  intro current id lowered certified
  exact preserves_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    root size certified

include bridge receiver stagePrepared observations extension semantic factories in
/-- The chosen Header and returned child pool stay literal. Registry equality
is required only for reflection; no Source/native grade equality is introduced. -/
theorem reflects_named
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
      header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) (size : Nat) :
    ReflectsAt bridge header.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support authority ready
  have root : RootAt compiled header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named] using
      (support.roots child selected).val
  intro current id lowered certified
  exact reflects_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    stageEq root size certified
end Named
end Meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCompilerTerminalCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerFactories
/-! The actual named compiler recipe supplies the callback and body used by
selected recursive caller support. The remaining inputs concern the original
Source, its static policy and the actual reached calls. The chosen recipe and
terminal packet remain fixed throughout certificate construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerFactories
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
  (OriginalConditions NamedAuthority NamedReady)
open CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes (Recipe)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- The actual compiler supplies a recipe for this exact terminal packet. -/
theorem recipe (packet : Terminal header) : Nonempty (Recipe header packet) :=
  CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.of_terminal packet

/-- Source admission remains independent of compilation. Every actual
selected child retains its own registry scope, evidence and parameter context. -/
structure Conditions {packet : Terminal header} (recipe : Recipe header packet)
    (stages : Staging.Recursive.Registry)
    (semanticFaults : FunctionCalls.FaultRep) where
  readFuel : Nat
  profile : PolicyFor recipe.policy
    (CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named) readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    header.reasonAt
  tree : Syntax header.function.source packet.expression
  original : ∀ child, stages.Closure header.function child →
    OriginalConditions compiled recipe.policy
      (CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named) readFuel
      header.context child header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) semanticFaults

variable {packet : Terminal header} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (selected : Recipe header packet)

/-- The actual compiler, its real child fuel and its cached specialization
construct all callback fields. No compiler-action equality is an input. -/
def authority (conditions : Conditions selected stages semanticFaults) :
    NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults) :=
  { policy := selected.policy
    body := selected.body
    compilation := CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named
    compilerFuel := packet.receipt.childFuel
    readFuel := conditions.readFuel
    native := compiled.indexed.base.callableContext
    active := []
    callables := selected.callables
    callback := selected.callback
    profile := conditions.profile
    tree := conditions.tree
    conditions := conditions.original }

/-- Call readiness refers to the certificate issued from this same compiler
recipe, rather than a freely chosen certificate or a body execution law. -/
def Ready (conditions : Conditions selected stages semanticFaults) : Prop :=
  NamedReady (authority selected conditions)

/-- Original typing and the actual accepted compiler action produce each
selected root internally, with the complete reached-call authority retained. -/
def support (conditions : Conditions selected stages semanticFaults)
    (ready : Ready selected conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport header stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named header packet)
      semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support
    (authority selected conditions) ready

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerFactories
end
