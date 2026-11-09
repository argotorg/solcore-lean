import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalSupport
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForItems
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOperators
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.DirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalCalls

/-!
# Lifting to staged Source: calls

Lifting of named, method and coerced calls: call and caller handlers, terminal, scoped and body lifting of each.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
/-! Internal call-head continuations for the shared structural expression proof.
Each continuation is indexed by an actual compiler receipt and its path in the
root certificate. Concrete invocation theorems construct these continuations
from strictly smaller body proofs and the reached protected state. Each port
retains independent staged preservation and bounded ordinary lifting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
open SelectedCompilationStageLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions) (stages : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (budget : Nat)
  (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
    invocation.source context reasonAt scope id code)

def Laws (certificate : GenericExpressionMeaning.Certificate) : Prop :=
  (∀ size, PreservesAt bridge context model stages invocation certificate faults size) ∧
  (∀ size, size ≤ budget → LiftsAt bridge context model stages invocation certificate size)

theorem Laws.entries {current : SourceCoreLocalCell.Scope}
    {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}
    (children : ∀ child code, (child, code) ∈ entries →
      Laws (context := context) (invocation := invocation) bridge model stages faults budget (Point current child code)) :
    Laws (context := context) (invocation := invocation) bridge model stages faults budget (RecursiveStageTupleMeaning.Entries current entries) := by
  constructor
  · intro size scope id lowered entry
    obtain ⟨rfl, member⟩ := entry
    exact (children id lowered member).1 size ⟨rfl, rfl, rfl⟩
  · intro size within scope id lowered entry
    obtain ⟨rfl, member⟩ := entry
    exact (children id lowered member).2 size within ⟨rfl, rfl, rfl⟩

def Direct : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

def Method : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

def Indirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    (∀ size, PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size) ∧
    (∀ size, size ≤ budget →
      (∀ childSize, childSize < size → LiftsAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) childSize) →
      (∀ childSize, PreservesAt bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults childSize) →
      LiftsAt bridge context model stages invocation (Point scope id code) size)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open SelectedCompilationStageBodyLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {terminal : Terminal header}
  (static : SelectedCompilationPhysicalMixedNamedTerminalSupport.Support
    (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal)
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)

local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include static selected certified in
/-- The actual terminal statement selects one strictly smaller ordinary child.
The internal root induction lifts it before reconstructing the same return. -/
theorem lifts {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner _packet keyPhysical physical slots
    size finalContext outcome after trace within
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      child.source terminal.expression header.function.body := by
    rw [stages.source selected]
    exact terminal.receipt.terminal
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique originalTerminal trace
  subst finalContext
  subst outcome
  let entered : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨initial, slots⟩, physical⟩
  have enteredAdmission : Admission physicalBridge header.context entered := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨node, found, _rawType, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  rw [← stages.source selected] at found sourceTyped
  let root := (static.roots child selected).val
  have meaning : LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      header.context model stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child) childSize :=
    children childSize (Nat.lt_of_lt_of_le strict within) root owner keyPhysical
  have prefixEq : root.compilation.administrativePrefix = 1 := (static.roots child selected).property.2.2
  rw [prefixEq] at meaning
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found sourceTyped environments heaps locals agrees typed
    entered enteredAdmission evaluated
  exact terminal_expression (terminal.receipt.head child (stages.source selected)) lifted

include selected in
/-- A factory's actual terminal lambda has no callable-body execution at
formation time. The ordinary atomic trace lifts with the same captures. -/
theorem formation {bodyRegistry : SourceCoreRawMetadata.Registry}
    (formation : SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
      header terminal) {budget : Nat} :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    _environments _heaps _locals _agrees _typed _initial _admitted _owner _packet _keyPhysical _physical _slots
    size finalContext outcome after trace _within
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      child.source terminal.expression header.function.body := by
    rw [stages.source selected]
    exact terminal.receipt.terminal
  obtain ⟨_childSize, plain, _strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique originalTerminal trace
  subst finalContext
  subst outcome
  obtain ⟨receipt⟩ := formation.formations child selected
  cases receipt with
  | inl receipt =>
    have found : child.source.lookupExpression? terminal.expression = some receipt.site.code.sourceNode := by
      simpa only [stages.source selected, header.agreement.source, receipt.identifier,
        CallableIndexedLambdaGeneration.closure, CallableIndexedNamedGeneration.source] using receipt.site.code.sourceFound
    have lifted := Staging.Recursive.Lifting.atomic_nonlocal (registry := stages)
      unique (lookupExpression?_sound found)
      (receipt.site.code.sourceForm.symm ▸ Staging.Recursive.AtomicForm.lambda _ _ _)
      receipt.coercions
      (by intro name binder same; rw [receipt.site.code.sourceForm] at same; cases same)
      evaluated.sound
    exact terminal_expression (terminal.receipt.head child (stages.source selected))
      (Staging.Recursive.Lifting.ExpressionLift.completed lifted)
  | inr receipt =>
    cases receipt with
    | inl receipt =>
      have found : child.source.lookupExpression? terminal.expression = some receipt.produced.site.code.sourceNode := by
        simpa only [stages.source selected, header.agreement.source, receipt.produced.identifier,
          CallableIndexedLambdaGeneration.closure, CallableIndexedNamedGeneration.source] using receipt.produced.site.code.sourceFound
      have lifted := Staging.Recursive.Lifting.atomic_nonlocal (registry := stages)
        unique (lookupExpression?_sound found)
        (receipt.produced.site.code.sourceForm.symm ▸ Staging.Recursive.AtomicForm.lambda _ _ _)
        receipt.coercions
        (by intro name binder same; rw [receipt.produced.site.code.sourceForm] at same; cases same)
        evaluated.sound
      exact terminal_expression (terminal.receipt.head child (stages.source selected))
        (Staging.Recursive.Lifting.ExpressionLift.completed lifted)
    | inr receipt =>
      have found : child.source.lookupExpression? terminal.expression = some receipt.produced.site.code.sourceNode := by
        simpa only [stages.source selected, header.agreement.source, receipt.produced.identifier,
          CallableIndexedLambdaGeneration.closure, CallableIndexedNamedGeneration.source] using receipt.produced.site.code.sourceFound
      have lifted := Staging.Recursive.Lifting.atomic_nonlocal (registry := stages)
        unique (lookupExpression?_sound found)
        (receipt.produced.site.code.sourceForm.symm ▸ Staging.Recursive.AtomicForm.lambda _ _ _)
        receipt.coercions
        (by intro name binder same; rw [receipt.produced.site.code.sourceForm] at same; cases same)
        evaluated.sound
      exact terminal_expression (terminal.receipt.head child (stages.source selected))
        (Staging.Recursive.Lifting.ExpressionLift.completed lifted)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedScopedLifting
/-! Actual named parameter entry supplies the physical slots, current authority,
and original frame used by the existing scoped flow engine. Every expression
child is discharged by the strictly smaller mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedScopedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open SelectedCompilationNamedScopedSupport (Support)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {receipt : Receipt header}
  (support : Support headers header stages receipt semanticFaults)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support globals selected semantic faithful observations assignmentInterpretation in
/-- The original named body starts at its genuine parameter entry. Completed
bodies retain the exact Source context and heap; stage rejection retains the
actual earlier prefix and skips the remaining effects. -/
theorem lifts [RecursiveStageMeaning.FaultTokens faults]
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages invocation budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet keyPhysical physical slots size finalContext outcome after trace within
  have originalPacket := packet keyPhysical.prefixZero globals
  let actualEntry := CallableIndexedOwnedLambdaViewHeads.nested_entry (caller := header) initial owner
    keyPhysical.prefixZero (originalPacket.observed owner header) originalPacket.carried originalPacket.bundle globals
  have prefixAgreement := CallableIndexedOwnedPhysicalLambdaCaptures.entry_prefix_for
    slots globals actualEntry environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix environments
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header) prefixAgreement
  have agrees : EnvironmentsAgree ξ
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) actual :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix agrees
    ((parameterScope header).length +
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  have packet := CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix.packet_take
    header owner initial originalPacket (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope header)
      (canonical.take ((parameterScope header).length +
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, List.length_cons, List.length_append,
        List.length_map, List.length_nil]
      omega
  let canonical := canonical.take ((parameterScope header).length +
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  let wrapped : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨⟨initial, retainedSlots⟩, physical⟩
  have nestedAdmitted : Admission physicalBridge header.context wrapped :=
    ⟨admitted.heap, admitted.rows⟩
  obtain ⟨expressionSyntax, collected⟩ := support.tree invocation selected
  rw [layouts] at collected
  have tree := collected.tree
  have catalogSites := collected.sites receiving
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions
      (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← stages.source selected] at assignmentDiagnostics
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape invocation.source true header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [canonical, globals, parameterScope] using packet.reference
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    support.certified.statements
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements invocation.source header.context header.function.body :=
    ⟨_, _, _, sourceTyped⟩
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  exact SelectedCompilationStageImperativeLifting.lifts_at
      physicalBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl header.registered
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : LiftsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) size :=
          children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (fun context size scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) faults size :=
          preservation size root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (by rw [stages.source selected]; exact header.unique)
      tree catalogSites semantic assignmentDiagnostics rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped
      reference read unmapped wrapped conditioned nestedAdmitted trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedScopedLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open SelectedCompilationPhysicalNamedBodySupport (Support)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageLiftBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {body : Body header}
  (support : Support (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
    (semanticFaults := semanticFaults) header body)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {faults : RecursiveStageMeaning.FaultRep}
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support profile certified extension selected semantic assignmentInterpretation in
theorem lifts [RecursiveStageMeaning.FaultTokens faults] {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  cases support with
  | terminal terminal static =>
    exact SelectedCompilationStageNamedTerminalLifting.lifts
      static selected certified children
  | formation terminal static globals =>
    exact SelectedCompilationStageNamedTerminalLifting.formation selected static
  | «scoped» body receipt compilation static =>
    exact SelectedCompilationStageNamedScopedLifting.lifts (semantic := semantic) (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions (CallableIndexedLambdaValues.identity_faithful compiled.indexed) (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
      selected extension body.layouts children preservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
/-! Actual static program support closes both ordinary call-head ports. The
only recursive input is lifting at strictly smaller ordinary trace grades;
staged preservation is supplied by the already closed physical family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open SelectedCompilationPhysicalProgramSupport (Support functions stages stagePrepared)
open SelectedCompilationStageLiftBounds (LiftsRootsAt preserves_roots)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics

include support issued extension in
theorem named_bodies {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget := by
  exact
    haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled issued)
    SelectedCompilationStageNamedBodyLifting.lifts (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension) (support.bodySupport header member)
      support.profile (support.certificates header member)
      (SelectedCompilationPhysicalProgramSupport.static_extension support extension) selected children
      (preserves_roots support issued extension)

private theorem named_descriptor (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.Root compiled headers (stages compiled)
    policy lowerBody compilation readFuel context invocation reasonAt scope expression lowered rawType
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
local notation "bridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots (callerBridge)

include support issued extension root owner keyPhysical in
theorem direct {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Direct bridge model (stages compiled) faults budget root.certificate := by
  intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence
  obtain ⟨⟨port, certified, shaped⟩⟩ := root.directReady compiler path
  have rows := SelectedCompilationDirectSourceTypes.source_types
    compiler port.toReady shaped root.runtime.signatures application
  have ordered := rows.1 ▸ sequence
  constructor
  · intro size childPreservation
    exact SelectedCompilationPhysicalDirectBounds.preserves
      owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
      (functions support) faults root.unique support.bodyTyping.function_ids certified shaped root.runtime
      size ordered childPreservation
      (fun selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension port.header port.member selected size)
  · intro size within childLift childPreservation
    obtain ⟨descriptor⟩ := named_descriptor port.header
    obtain ⟨sidecar, _prepared, _same, selected, _declaration, _local, _evidence, _marker, _analysis⟩ :=
      CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected port.sourceAt port.prepared port.aligned
        (stagePrepared compiled) descriptor
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view port.sourceAt] at selected
    exact SelectedCompilationStageDirectLifting.direct
      owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
      (functions support) faults root.runtime.requirements.idsUnique root.unique support.bodyTyping.function_ids
      certified root.runtime selected size ordered childLift childPreservation
      (named_bodies support issued extension
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within)) port.header port.member selected)

include support issued extension root owner keyPhysical in
theorem indirect {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Indirect bridge model (stages compiled) faults budget root.certificate := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled issued)
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled support.issued)
  intro fuel current id callee ids metadata code types compiler path sequence
  obtain ⟨port⟩ := root.callsReady compiler path
  have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
      current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
  constructor
  · intro size childPreservation
    exact SelectedCompilationPhysicalIndirectHeadBounds.preserves
      (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued)
      (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
      bridge (fun state => state.physical) support.owners issued (stagePrepared compiled) rfl
      support.profile support.bodyTyping support.certificates root.runtime root.unique root.actualFunctionType
      (SelectedCompilationPhysicalProgramSupport.observations support) support.closurePackets support.closureSupport
      support.bodies compiler port calleeCertified sequence size childPreservation size
      (fun child _smaller => preserves_roots support issued extension child)
      (fun header member {_} selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension header member selected size) (Nat.le_refl _)
  · intro size within childLift childPreservation
    exact SelectedCompilationStageIndirectLifting.indirect support bridge (fun state => state.physical)
      compiler port root.runtime root.actualFunctionType root.unique size calleeCertified sequence
      childLift childPreservation
      (fun header member child selected => named_bodies support issued extension
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within)) header member selected)
      (fun association => SelectedCompilationStageClosurePacketRoots.association_of_roots (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed) (observations := SelectedCompilationPhysicalProgramSupport.observations support) (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
        (functions support) association (support.closurePackets association)
        (support.closureSupport association) support.owners
        (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
        (preserves_roots support issued extension))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open DataExpressionSequence
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageLiftSequence (SequenceLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem values_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsAt program budget context invocation.evidence
      invocation.source environment before ids sources after) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨_, _, .nil, .completed⟩
  | single found generated =>
    cases execution with
    | cons head strict tail =>
      cases tail
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.value head)
      cases adapted with
      | completed => exact ⟨_, _, .cons trace .nil, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head strict rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
        cases restAdapted with
        | completed => exact ⟨_, _, .cons trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem values (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsAt program budget context invocation.evidence
      invocation.source environment before ids sources after) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  apply values_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

private theorem fault_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsFaultAt program budget context invocation.evidence
      invocation.source environment before ids reason after) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  induction tree generalizing mapping world actual actualContext before store ξ reason after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed strict =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail _ _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed strict =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail head strict rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        strict
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
        cases restAdapted with
        | completed => exact ⟨_, _, .tailFault trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem fault (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : CallablePreparedOperatorSourceBounds.ArgumentsFaultAt program budget context invocation.evidence
      invocation.source environment before ids reason after) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  apply fault_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
/-! Staged method invocation enters the actual marked parameter prefix and
restores the caller from the body's reached pool. Both callbacks receive the
real complete cache and slot layout, and preserve semantic and stage faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry)
open CallableIndexedOwnedPreparedStagedMethodInvocationEntries
open SelectedCompilationStageBodyLiftBounds
open Staging.Recursive.Lifting (Adapted)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)


variable {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] installed.canonical)

def LiftBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (_reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  ∀ {size finalContext bodyOutcome after},
    RecursiveNamedCallBounds.FunctionOutcome program size sourceAt.context child.evidence child.source entry.environment
      entry.heap generation.statements finalContext bodyOutcome after →
    size < budget →
    BodyLift program stages true child sourceAt.context entry.environment entry.heap
      generation.statements finalContext bodyOutcome after

def LiftContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    LiftBodyAt (stages := stages) (child := child)
      generation sourceAt functions budget entry reached

/-- The result retains the actual allocated Source frame and the complete
body derivation. An earlier stage rejection carries its own reached heap. -/
def MethodLift (arguments : List Dynamic.Value) (before : Dynamic.Heap)
    (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ environment bound finalContext staged result reached,
    Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
    Staging.Recursive.StatementsIn program stages true child sourceAt.context environment bound
      generation.statements finalContext staged reached ∧
    Staging.Recursive.BodyResult sourceBody.resultType staged result ∧
    Adapted plain after result reached

include sourceAt installed represented sameFrame heaps physical slots in
/-- The original body trace enters the exact installed parameter state before
using the internally supplied selected-body lift. -/
theorem lifts_invocation (budget : Nat)
    (selected : stages.Closure (methodFunction generation sourceBody dictionary) child)
    (bodyMeaning : LiftContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) generation sourceAt functions installed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after)
    (within : size ≤ budget) :
    MethodLift (program := program) (stages := stages) (child := child) generation sourceAt arguments before outcome after := by
  have parameters : MonoBindersExtend (methodFunction generation sourceBody dictionary).source.owner
      (methodFunction generation sourceBody dictionary).context (methodFunction generation sourceBody dictionary).parameters
      sourceAt.types sourceAt.context := by
    simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using sourceAt.extended
  have arity : (methodFunction generation sourceBody dictionary).parameters.length = arguments.length := by
    rw [sourceAt.frame.parameters, sourceAt.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨bodySize, environment, bound, allocated, sourceTrace, strict⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields sourceAt.frame.source sourceAt.frame.context
      sourceAt.frame.parameters sourceAt.frame.result sourceAt.frame.roots parameters arity trace
  obtain ⟨finalContext, control, plainBody, exit⟩ := SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation sourceAt functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at plainBody
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨lastContext, staged, reached, bodyTrace, adapted⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property
      (by simpa only [stages.source selected, stages.evidence selected, methodFunction, CallableCoercionMethodFrame.view] using plainBody)
      (Nat.lt_of_lt_of_le strict within)
  obtain ⟨result, converted, resultAdapted⟩ := adapted.exit (sourceAt.frame.result ▸ exit)
  exact ⟨entry.environment, entry.heap, lastContext, staged, result, reached,
    sourceAt.frame.parameters ▸ entry.allocation, bodyTrace, converted, resultAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open SelectedCompilationStageLiftBounds (LiftsAt)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (selection : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context invocation.evidence port.principal.traitName port.principal.methodName receipt.node.requirements
    port.principal.sourceBody port.principal.dictionary)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def BodyLifts (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationStageMethodInvocationLifting.LiftContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child)
      port.principal.cached.compilation port.sourceAt functions installed budget


include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem raw_trace {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodies : BodyLifts (headers := headers) (receiving := receiving) owner receipt port functions size)
    (typed : ExpressionHasType invocation.source context id receipt.node.type)
    {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
      environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (original : CallablePreparedOperatorSourceBounds.RawTraceAt (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence port.principal.dictionary invocation.source environment before
      receipt.arguments port.principal.sourceBody outcome after) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id outcome after := by
  obtain ⟨orderedTyping, _sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  cases original with
  | argumentFault failed =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageOperatorArgumentsLifting.fault bridge
      size sequence unique orderedTyping childLift preservation environments heaps locals agrees actualTyped initial admitted failed
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .completed⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .rejected origin call reason _⟩
  | apply evaluated called strict =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageOperatorArgumentsLifting.values bridge
      size sequence unique orderedTyping childLift preservation environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨values, middleStore, middleMap, middleWorld, _argumentsEvaluated, represented, middleHeaps,
          _argumentMaps, _argumentWorlds, _argumentFrame, _argumentMetadata, reached, _related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge grade sequence unique orderedTyping
          (fun size _ => preservation size) environments heaps locals agrees actualTyped initial admitted measured (Nat.le_refl _)
      obtain ⟨headerHeap, headerArguments, _result⟩ :=
        SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
          post.at_values.heap post.values_typed
      have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port represented
      obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
        port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
        (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
      have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
        rw [capture.canonical_eq]
        exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
      obtain ⟨bodyEnvironment, bound, finalContext, stagedBody, result, finalHeap, allocated, bodyTrace, matched, adapted⟩ :=
        SelectedCompilationStageMethodInvocationLifting.lifts_invocation
          port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
          (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size port.staged
          (bodies (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows port.staged)
          called (Nat.le_of_lt strict)
      obtain ⟨bodyGrade, bodyMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace bodyTrace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.applied receipt port
        measured port.staged allocated bodyMeasured matched
      exact ⟨_, _, lifted.sound, adapted⟩

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem method {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodies : BodyLifts (headers := headers) (receiving := receiving) owner receipt port functions size) :
    LiftsAt bridge context model stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  exact raw_trace owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime
    size sequence childLift preservation bodies typed environments heaps locals agrees actualTyped initial admitted
    (SelectedCompilationStageOperatorSourceTrace.source_inv receipt port unique runtime.requirements.idsUnique execution)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
/-! The actual installed method and marked parameter entry supply admission,
physical cache slots and the frame used by the existing scoped flow engine.
Every reached expression is discharged by the strict mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodScopedSupport (Packet Support parameterScope nativePrefix)
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationStageMethodInvocationLifting

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include certified beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing principal packet.sourceAt certified
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include packet in
private theorem prefix_agrees
    {localScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {map : LocationMap} {typing : StoreTyping} {environment : Dynamic.Environment}
    {administrative : Core.Context} {location : Location}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 localScope canonical)
    (reference : canonical[localScope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      map typing (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)
      localScope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix principal).length (nativePrefix principal)
      (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative) := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext localScope ++
        SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero => simp [nativePrefix, packet.sourceAt.parameterType]
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have atType := tag (slots slot signature selected)
      have outside : ¬ localScope.length + 1 + slot < localScope.length := by omega
      have offset : localScope.length + 1 + slot - localScope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag reference
      have outside : ¬ localScope.length + 1 + compiled.indexed.base.globals.length < localScope.length := by omega
      have offset : localScope.length + 1 + compiled.indexed.base.globals.length - localScope.length =
          compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
/-- Actual parameter allocation supplies the entire Source body entry. -/
theorem source_continuation [RecursiveStageMeaning.FaultTokens faults]
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size)
    (preservation : ∀ size, PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    LiftContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome after trace within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      principal.sourceBody.source
      (fun site root => principal.cached.diagnostics.placeReason principal.named.signature.key site root none)
      (fun site root raw => principal.cached.diagnostics.placeReason principal.named.signature.key site root (some raw)) registry
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions
      (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
  rw [← sourceEq] at assignmentDiagnostics
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  exact
    SelectedCompilationStageImperativeLifting.lifts_at
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : LiftsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (fun context size scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := preservation size root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      unique collected.tree (collected.sites registry) semantic assignmentDiagnostics rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt within) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting
/-! The genuine method parameter entry supplies admission and the complete
physical cache. Strict expression induction closes the actual terminal body;
the static support carries neither body execution nor a semantic callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodBodySupport (Packet Support)
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open SelectedCompilationStageBodyLiftBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationStageMethodInvocationLifting

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "point" => Point (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child

include certified beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing principal packet.sourceAt certified
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- The actual method parameter frame supplies heap typing and retained
callable origins before lifting the strictly smaller terminal expression. -/
theorem source_continuation (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size) :
    LiftContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome after trace within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal child.source
      packet.expression principal.cached.compilation.statements := sourceEq ▸ packet.receipt.terminal
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique terminal trace
  subst finalContext
  subst bodyOutcome
  obtain ⟨node, found, _rawType, typed⟩ := SelectedCompilationMethodBodySupport.child_typed
    principal packet certified selected
  obtain ⟨root⟩ := support.roots child selected
  have meaning : LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point childSize :=
    children childSize (Nat.lt_trans strict within)
      (SelectedCompilationMixedRootSupport.RootAt.ofMethod root.toRootAt) owner keyPhysical
  rw [root.prefixLength] at meaning
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found typed entry.environments entry.heaps entry.locals
    entry.lookups entry.actualTyped initial admitted evaluated
  exact terminal_expression (packet.receipt.head child sourceEq) lifted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
/-! Static method packet dispatch preserves the same genuine parameter entry
and current physical authority in either body form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open SelectedCompilationMethodBodies (Packet Support)
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsRootsAt)
open SelectedCompilationStageMethodInvocationLifting

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
theorem source_continuation [RecursiveStageMeaning.FaultTokens faults]
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size)
    (preservation : ∀ size, PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    LiftContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationStageMethodTerminalLifting.source_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      children
  | «scoped» packet =>
    exact SelectedCompilationStageMethodScopedLifting.source_continuation (semantic := semantic) (assignmentInterpretation := assignmentInterpretation)
      principal packet support certified functions faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children preservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds (LiftsRootsAt preserves_roots)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.Root compiled headers (stages compiled) policy lowerBody compilation readFuel
    context invocation reasonAt scope expression lowered rawType
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations

include issued extension in
theorem method {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Method (callerBridge).forgetSlots model (stages compiled) faults budget root.certificate := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled issued)
  intro fuel current id code types compiler path sequence
  obtain ⟨⟨port, selection⟩⟩ := root.methodReady compiler path
  obtain ⟨packet, sourceAtEq, static⟩ := support.methods compiler port selection
  have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal packet.sourceAt selection
  constructor
  · intro size childMeaning
    have bodies : SelectedCompilationMethodHeadBounds.SourceBodies
        (headers := headers) (receiving := receiving.result.context.registry) owner compiler port (functions support) faults size := by
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
        heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
        simpa only [sourceAtEq] using argumentsTyped
      simpa only [sourceAtEq] using
        SelectedCompilationMethodBodyBounds.source_continuation (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed) (observations := SelectedCompilationPhysicalProgramSupport.observations support) (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
          port.principal packet static certified (functions support) selected installed owner keyPhysical caller
          heapTyped packetArguments stable (static_extension support extension) size
          (fun smaller _ => preserves_roots support issued extension smaller)
    intro actualScope actualId actualCode point actual found typed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans compiler.metadata.found)
    have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
      root.catalog selection root.runtime root.unique typed
    have ordered := SelectedCompilationStageLiftConstructors.tree_types sequence root.unique rows.1 ▸ sequence
    intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
    exact SelectedCompilationMethodHeadBounds.preserves
      owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
      (fun state => state.base.property) (functions support) faults root.unique root.catalog selection
      root.runtime size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
  · intro size within childLift preservation
    have bodies : SelectedCompilationStageMethodLifting.BodyLifts
        (headers := headers) (receiving := receiving.result.context.registry) owner compiler port (functions support) size := by
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
        heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
        simpa only [sourceAtEq] using argumentsTyped
      simpa only [sourceAtEq] using
        SelectedCompilationStageMethodBodyLifting.source_continuation (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed) (observations := SelectedCompilationPhysicalProgramSupport.observations support) (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
          port.principal packet static certified (functions support) selected installed owner keyPhysical caller
          heapTyped packetArguments stable (static_extension support extension) size
          (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
          (fun grade => preserves_roots support issued extension grade)
    intro actualScope actualId actualCode point actual found typed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans compiler.metadata.found)
    have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
      root.catalog selection root.runtime root.unique typed
    have ordered := SelectedCompilationStageLiftConstructors.tree_types sequence root.unique rows.1 ▸ sequence
    intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
    exact SelectedCompilationStageMethodLifting.method
      owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
      (fun state => state.base.property) (functions support) faults root.unique root.catalog selection
      root.runtime size ordered childLift preservation bodies ⟨rfl, rfl, rfl⟩ found typed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting
/-! The exact finite compiler tree supplies ordinary-to-staged child lifting.
Each call continuation carries its actual receipt and path in that tree.
Closed staged preservation advances the physical state between ordered children;
its execution grade is independent of the ordinary lifting budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls DirectCalls MethodCalls)
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority (IndexReady)
universe u
open CallableLambdaBodyReachability
open SelectedCompilationStageLiftBounds
open SelectedCompilationStageCallerHeadHandlers (Laws Direct Method Indirect)

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

section Generic

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (indexObservations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions
    (CallableIndexedLambdaValues.Identity compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "bridge" => callerBridge

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include callerBridge receiver functions runtime unique
  observations functionTypes indexObservations extension semantic sameLedger runtimeLedger uninitializedOn in
private theorem preserves [FunctionCalls.FaultTokens semanticFaults] {budget rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId))
    (directHeads : Direct bridge model stages callFaults budget root)
    (methodHeads : Method bridge model stages callFaults budget root)
    (indexReady : IndexReady root)
    (indirectHeads : Indirect bridge model stages callFaults budget root) :
    ∀ size, PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
  intro size
  exact SelectedCompilationSharedCallerBounds.preserves_reached_with_functions
    bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
    sameLedger runtimeLedger uninitializedOn size root reached
    (fun compiler path callee application sequence childSize _within =>
      (directHeads compiler path callee application sequence).1 childSize)
    (fun compiler path sequence childSize _within =>
      (methodHeads compiler path sequence).1 childSize)
    indexReady
    (fun compiler path sequence childSize _within =>
      (indirectHeads compiler path sequence).1 childSize)
    size (Nat.le_refl _)

include callerBridge receiver functions runtime unique
  observations functionTypes indexObservations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Finite compiler structure supplies every ordered child lift. Call heads
are indexed by their actual compiler receipt and path in this same tree. -/
theorem laws [FunctionCalls.FaultTokens semanticFaults] (budget : Nat) {rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    Direct bridge model stages callFaults budget root →
    Method bridge model stages callFaults budget root → IndexReady root →
    Indirect bridge model stages callFaults budget root →
    Laws (context := context) (invocation := invocation) bridge model stages callFaults budget (Point rootScope rootId rootCode) := by
  revert reached
  induction root with
  | proxy receipt =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.proxy receipt) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      intro size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationStageProxyLifting.lifts bridge functions unique size (.proxy receipt)
  | leaf tree =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.leaf tree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      intro size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationStageReadProductLifting.lifts bridge functions extension
        sameLedger runtimeLedger unique size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.unary metadata form found inputType outputType unaryProfile child) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside))
      intro size within
      exact SelectedCompilationStageLiftOperators.unary bridge size
        (childCode := ⟨core.operandType, childCode⟩) metadata form unique found
        (children := RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)])
        ⟨rfl, by simp⟩ (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within))
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.index header keyFound form sourceType firstTree secondTree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihFirst reached0
            (fun compiler inside => directHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))

        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihSecond reached1
            (fun compiler inside => directHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (firstTree := firstTree) (secondTree := secondTree) inside))

      intro size within
      exact SelectedCompilationStageIndexLifting.index bridge header keyFound form unique
        (children := RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ size
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.binary metadata form leftFound rightFound leftType rightType outputType binaryProfile first second) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside))
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside))
      intro size within
      exact SelectedCompilationStageLiftOperators.binary bridge size
        (leftCode := ⟨operatorMode.operandType operator, leftCode⟩)
        (rightCode := ⟨operatorMode.operandType operator, rightCode⟩) metadata form unique leftFound rightFound
        (children := RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihCondition reached0 (fun compiler inside => directHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihThen reached1 (fun compiler inside => directHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          exact ihElse reached2 (fun compiler inside => directHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
      intro size within
      exact SelectedCompilationStageLiftConditional.conditional bridge functions size
        (conditionCode := ⟨.bool, conditionCode⟩) (thenCode := ⟨type, thenCode⟩)
        (elseCode := ⟨type, elseCode⟩) metadata form unique
        (children := RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)])
        rfl ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ ⟨rfl, by simp⟩
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.group metadata form innerFound sourceType child) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (Point rootScope inner code) := by
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside))
      intro size within current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationStageGroupLifting.group bridge unique size
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within))
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.tuple header sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside))
      intro size within
      exact SelectedCompilationStageLiftConstructors.tuple bridge size header.metadata header.form unique sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.constructor header form admissible ranges count nodes sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside))

      intro size within
      exact SelectedCompilationStageLiftConstructors.constructor bridge size header.metadata form unique
        (CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges) sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.builtin compiler calleeTyped sourceType nativeTypes sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside))

      intro size within
      exact SelectedCompilationStageLiftBuiltin.builtin bridge size
        compiler.metadata compiler.form unique sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.direct compiler calleeTyped application sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))

      intro size within
      exact (directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.method compiler sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))

      intro size within
      exact (methodHeads compiler (.here sequence children) sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
        sameLedger runtimeLedger uninitializedOn (.call compiler sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => indexReady indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside))
      intro size within
      exact (indirectHeads compiler (.here sequence children) sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1

include callerBridge receiver functions runtime unique
  observations functionTypes indexObservations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Projection consumed by the ordinary-trace induction. All child laws are
constructed by the finite certificate recursion above. -/
theorem lifts_reached_with_functions [FunctionCalls.FaultTokens semanticFaults] (budget : Nat) {rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId))
    (directHeads : Direct bridge model stages callFaults budget root)
    (methodHeads : Method bridge model stages callFaults budget root)
    (indexReady : IndexReady root)
    (indirectHeads : Indirect bridge model stages callFaults budget root)
    (size : Nat) (within : size ≤ budget) :
    LiftsAt bridge context model stages invocation (Point rootScope rootId rootCode) size := by
  exact (laws bridge receiver functions runtime unique observations functionTypes indexObservations extension semantic
    sameLedger runtimeLedger uninitializedOn budget root reached
    directHeads methodHeads indexReady indirectHeads).2 size within

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.Root compiled headers (stages compiled) policy lowerBody compilation readFuel
    context invocation reasonAt scope expression lowered rawType
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics

include support issued extension root owner keyPhysical in
theorem lifts (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model (stages compiled) semanticFaults size) :
    LiftsAt (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
      compilation.administrativePrefix).forgetSlots context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) budget := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled support.issued)
  let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
  intro current id code point
  exact SelectedCompilationStageSharedCallerLifting.lifts_reached_with_functions
    callerBridge.forgetSlots issued (functions support) root.runtime root.unique
    (observations support) (CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views support.profile)
    (observations support) (static_extension support extension) (semantic_extension support issued extension)
    root.sameLedger root.runtimeLedger root.uninitialized budget root.certificate (.root (by simp))
    (SelectedCompilationStageCallHandlers.direct support issued extension root owner keyPhysical children)
    (SelectedCompilationStageMethodHeadHandlers.method support issued extension root owner keyPhysical children)
    root.indexReady
    (SelectedCompilationStageCallHandlers.indirect support issued extension root owner keyPhysical children)
    budget (Nat.le_refl _) point

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)
open SelectedCompilationStageCoercionLiftBounds
open SelectedCompilationCoercionInvocationBounds (represented_arguments)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {sourceCaller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation sourceCaller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def LiftBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationStageMethodInvocationLifting.LiftContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child)
      port.principal.cached.compilation port.sourceAt functions installed budget

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {source : Dynamic.Value} {value : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source source value call.signature.parameterType)
  (headerHeap : Dynamic.HeapWellTyped port.principal.sourceFunction.context before)
  (headerArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context before [source] port.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows pool)
  (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)


private theorem source_body
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : StepOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      before coercion source outcome after) :
    ∃ bodySize, RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      bodySize port.principal.sourceBody port.principal.dictionary before [source] outcome after ∧
      bodySize < size := by
  cases trace with
  | value trace =>
    cases trace with
    | primitive absent _ => exact False.elim (absent _ _ port.selected)
    | method selected invoked =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ selected
      exact ⟨_, .value invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault trace =>
    cases trace with
    | requirement fault =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger step.selectedMethod port.selected fault)
    | primitiveInput absent _ _ => exact False.elim (absent _ _ port.selected)
    | method selected failed =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ selected
      exact ⟨_, .fault failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include ownerFrame physical slots heaps represented headerHeap headerArguments stable certified in
/-- The original selected conversion enters the actual installed method frame.
The result retains either its complete ordinary outcome or an earlier genuine
stage rejection, including the heap reached before rejection. -/
theorem lifts (budget : Nat)
    (bodyMeaning : LiftBodies (headers := headers) (receiving := receiving) step port owner functions budget)
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : StepOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      before coercion source outcome after)
    (within : size ≤ budget) :
    StepLift (Program.ofChecked compiled.sourceProgram) stages invocation context before coercion source outcome after := by
  obtain ⟨bodySize, sourceTrace, strict⟩ := source_body step port ledger trace
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  obtain ⟨environment, bound, finalContext, staged, result, reached, allocated, bodyTrace, matched, adapted⟩ :=
    SelectedCompilationStageMethodInvocationLifting.lifts_invocation
      port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
      (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget port.staged
      (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable port.staged)
      sourceTrace (Nat.le_of_lt (Nat.lt_of_lt_of_le strict within))
  exact ⟨result, reached,
    .coercionMethod port.selected port.sourceAt.frame.roots port.staged port.sourceAt.extended allocated bodyTrace matched,
    adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
open SelectedCompilationStageCoercionLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def LiftBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      SelectedCompilationStageCoercionInvocationLifting.LiftBodies
        (headers := headers) (receiving := receiving) step port owner functions budget ∧ LiftBodies tail budget

private inductive PathChildren (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap) (step : SourceInference.CoercionStep)
    (steps : List SourceInference.CoercionStep) (input : Dynamic.Value) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | head {child reason after}
      (failed : StepOutcome program child context evidence before step input (.fault reason) after)
      (smaller : child < size) : PathChildren program context evidence before step steps input size (.fault reason) after
  | cons {headSize tailSize converted middle plain after}
      (head : StepOutcome program headSize context evidence before step input (.value converted) middle)
      (tail : PathOutcome program tailSize context evidence middle steps converted plain after)
      (headLess : headSize < size) (tailLess : tailSize < size) :
      PathChildren program context evidence before step steps input size plain after

private theorem path_children {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {step : SourceInference.CoercionStep}
    {steps : List SourceInference.CoercionStep} {input : Dynamic.Value} {size : Nat} {plain : Dynamic.ExpressionOutcome}
    (trace : PathOutcome program size context evidence before (step :: steps) input plain after) :
    PathChildren program context evidence before step steps input size plain after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | cons head tail =>
      exact .cons (.value head) (.value tail)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault failed =>
    cases failed with
    | head failed => exact .head (.fault failed) (SourceExecutionSize.child_lt_stepSize (by simp))
    | tail head failed =>
      exact .cons (.value head) (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

variable {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (ownerFrame : owner.key.frameLocation = 0)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {sourceValue : Dynamic.Value} {nativeValue : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world source sourceValue nativeValue input.type)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (valueTyped : Dynamic.ValueHasType context before sourceValue source)
  (stable : StableRows pool)

include ownerFrame runtime ledger physical slots agrees heaps represented heapTyped valueTyped stable in
theorem lifts (budget : Nat)
    (bodyMeaning : LiftBodies (headers := headers) (receiving := receiving) owner functions chain budget)
    (preservation : ∀ grade, SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain grade)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PathOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence before steps sourceValue outcome after)
    (within : size ≤ budget) :
    PathLift (Program.ofChecked compiled.sourceProgram) stages invocation context before steps sourceValue outcome after := by
  induction chain generalizing mapping world before store sourceValue nativeValue size outcome after with
  | nil =>
    cases trace with
    | value evaluated => cases evaluated; exact ⟨_, _, .coercionsNil, .completed⟩
    | fault failed => cases failed
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
    have certified := (preservation 0).1.1
    obtain ⟨headerHeap, headerArguments⟩ :=
      SelectedCompilationCoercionInvocationBounds.source_arguments step port certified runtime heapTyped valueTyped
    have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
        sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
    cases path_children trace with
    | head failed smaller =>
      obtain ⟨staged, reached, head, adapted⟩ := SelectedCompilationStageCoercionInvocationLifting.lifts
        step port owner functions pool ownerFrame physical slots heaps inputRep headerHeap headerArguments stable
        certified budget bodyMeaning.1 ledger failed (Nat.le_trans (Nat.le_of_lt smaller) within)
      cases adapted with
      | completed => exact ⟨_, _, .coercionsFault head, .completed⟩
      | rejected origin call reason reached => exact ⟨_, _, .coercionsFault head, .rejected origin call reason _⟩
    | cons head tailTrace headLess tailLess =>
      obtain ⟨staged, reachedHeap, headTrace, adapted⟩ := SelectedCompilationStageCoercionInvocationLifting.lifts
        step port owner functions pool ownerFrame physical slots heaps inputRep headerHeap headerArguments stable
        certified budget bodyMeaning.1 ledger head (Nat.le_trans (Nat.le_of_lt headLess) within)
      cases adapted with
      | rejected origin call reason reached => exact ⟨_, _, .coercionsFault headTrace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨grade, sized⟩ := Staging.Recursive.Size.CoercionStep.of_trace headTrace
        obtain ⟨converted, middleStore, middleMap, middleWorld, _invoked, resultRep, middleHeaps,
            _maps, _worlds, frame, _metadata, ⟨reached, _related⟩, headPreserved⟩ :=
          SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame
            physical slots agrees heaps inputRep headerHeap headerArguments stable certified grade
            (preservation grade).1.2 ledger sized (Nat.le_refl _)
        cases resultRep with
        | value convertedRep =>
          have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
            step port certified runtime (headPreserved _ rfl)
          have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
          have nextRep := convertedRep
          rw [← middleType] at nextRep
          obtain ⟨outcome, after, tailTrace, adapted⟩ := ih reached (physical.extend frame) middleHeaps nextRep
            converted.heap_typed converted.value_typed (StableRows.after_administrative pool reached stable frame)
            bodyMeaning.2 (fun grade => (preservation grade).2) tailTrace (Nat.le_trans (Nat.le_of_lt tailLess) within)
          exact ⟨outcome, after, .coercionsCons headTrace tailTrace, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open SelectedCompilationPhysicalRawDirectBounds (RawPreservesAt)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
open SelectedCompilationStageCoercionLiftBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (ownerFrame : owner.key.frameLocation = 0)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  {stages : Staging.Recursive.Registry} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller receipt.available scope node callables context invocation stages
    node.rawType node.type receipt.operand node.coercions output calls)
  (nonempty : node.coercions ≠ [])
  (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (typed : ExpressionHasType invocation.source context id node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
    environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission callerBridge.forgetSlots context initial)

include physical slots ownerFrame chain nonempty unique runtime ledger typed environments heaps locals agrees actualTyped admitted in
theorem lifts (budget : Nat)
    (rawLift : ∀ {size plain after}, RawOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before node.form node.requirements node.coercions plain after → size ≤ budget →
      RawLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before
        node.form node.requirements node.coercions plain after)
    (rawPreservation : ∀ size, RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationStageCoercionPathLifting.LiftBodies
      (headers := headers) (receiving := receiving) owner functions chain budget)
    (bodyPreservation : ∀ grade, SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain grade)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before id outcome after) (within : size ≤ budget) :
    Staging.Recursive.Lifting.ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context
      environment before id outcome after := by
  cases SelectedCompilationStageCoercedSource.branches unique receipt.found receipt.form trace with
  | fault raw smaller =>
    obtain ⟨staged, reached, rawTrace, adapted⟩ := rawLift raw (Nat.le_trans (Nat.le_of_lt smaller) within)
    cases adapted with
    | completed => exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .rejected origin call reason _⟩
  | value raw path rawLess pathLess =>
    obtain ⟨staged, reachedHeap, rawTrace, adapted⟩ := rawLift raw (Nat.le_trans (Nat.le_of_lt rawLess) within)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨grade, sized⟩ := Staging.Recursive.Size.RawForm.of_trace rawTrace
      obtain ⟨native, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          _maps, _worlds, frame, _metadata, middleState, _related, rawPost⟩ :=
        rawPreservation grade typed environments heaps locals agrees actualTyped initial admitted sized
      cases represented with
      | value valueRep =>
        obtain ⟨staged, reachedHeap, pathTrace, adapted⟩ :=
          SelectedCompilationStageCoercionPathLifting.lifts owner functions faults chain ownerFrame runtime ledger
            (callerBridge.pool middleState) (physical middleState) (slots middleState) agrees middleHeaps valueRep
            rawPost.at_value.2.heap rawPost.at_value.1
            (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
              (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
            budget bodyMeaning bodyPreservation path (Nat.le_trans (Nat.le_of_lt pathLess) within)
        exact ⟨staged, reachedHeap,
          .coercedValue (lookupExpression?_sound receipt.found) nonempty rawTrace pathTrace, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
/-! The shared numerical induction supplies every conversion body from the
actual terminal packet, preserving the exact SourceAt and reached caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsRootsAt)
open SelectedCompilationMixedRootSupport (CoercionMethods)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (support : CoercionMethods headers semanticFaults chain)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include keyPhysical support in
theorem lift_bodies (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size) :
    SelectedCompilationStageCoercionPathLifting.LiftBodies
      (headers := headers) (receiving := receiving) owner functions chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, certified, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [SelectedCompilationMethodBodies.Packet.sourceAt, sourceAt] using
        SelectedCompilationStageMethodTerminalLifting.source_continuation
          port.principal packet static certified functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget children


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics

include support issued extension in
private theorem named_bodies {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget := by
  exact
    haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled issued)
    SelectedCompilationStageNamedBodyLifting.lifts (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension) (support.bodySupport header member)
      support.profile (support.certificates header member)
      (SelectedCompilationPhysicalProgramSupport.static_extension support extension) selected children
      (preserves_roots support issued extension)

private theorem named_descriptor (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.CoercedDirectRoot compiled headers (stages compiled)
    policy lowerBody compilation readFuel context invocation reasonAt scope expression lowered rawType
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
local notation "bridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots callerBridge

include support issued extension root owner keyPhysical in
theorem lifts (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    LiftsAt bridge context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) budget := by
  intro current id code point actual found typed mapping world administrativeContext environment canonical actualEnvironment
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initialState admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans root.actual.found)
  obtain ⟨types, _callee, application, argumentTyping⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types root.actual root.unique typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types root.actual root.port.toReady root.shape root.runtime.signatures application
  have argumentTypes := (SelectedCompilationStageLiftConstructors.tree_types root.argumentTree root.unique argumentTyping).trans rows.1
  have ordered := argumentTypes ▸ root.argumentTree
  have preservation := preserves_roots support issued extension
  have rawPreservation := SelectedCompilationPhysicalCoercedDirectRawBounds.preserves
    (receiving := receiving.result.context.registry)
    root support.bodyTyping.function_ids owner keyPhysical (functions support) faults
  have rawAll (size : Nat) : SelectedCompilationPhysicalRawDirectBounds.RawPreservesAt
      (context := context) (receiving := receiving.result.context.registry) owner root.actual callerBridge
      (functions support) faults (stages compiled) size := by
    exact rawPreservation size (fun child _ => preservation child)
      (fun grade _ {_} selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension root.port.header root.port.member selected grade) size (Nat.le_refl _)
  have paths := SelectedCompilationStagePhysicalCoercionMethods.lift_bodies
    owner keyPhysical (functions support)
    root.chain root.methods budget children
  have pathsPreserved (size : Nat) := SelectedCompilationPhysicalCoercionMethodBounds.source_bodies
    owner keyPhysical (functions support) faults
    root.chain root.methods size (fun child _ => preservation child)
  apply SelectedCompilationStageCoercedExpressionLifting.lifts
    owner root.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
    keyPhysical.frame (functions support) faults root.chain root.nonempty root.unique root.runtime root.ledger typed
    environments heaps locals agrees actualTyped initialState admitted budget
    ?_ rawAll paths pathsPreserved trace (Nat.le_refl _)
  intro size plain after raw within
  obtain ⟨descriptor⟩ := named_descriptor root.port.header
  obtain ⟨sidecar, _prepared, _same, selected, _declaration, _local, _evidence, _marker, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected root.port.sourceAt root.port.prepared root.port.aligned
      (stagePrepared compiled) descriptor
  rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view root.port.sourceAt] at selected
  have childLifts : ∀ smaller, smaller < size → LiftsAt bridge context model (stages compiled) invocation root.argumentCertificate smaller := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (SelectedCompilationMixedRootSupport.RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  have childPreservation : ∀ grade, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model (stages compiled) invocation root.argumentCertificate faults grade := by
    intro grade current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact preservation grade (SelectedCompilationMixedRootSupport.RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationStageRawDirectLifting.raw_direct
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical (fun state => state.physical)
    (functions support) faults root.unique support.bodyTyping.function_ids root.certified root.shape root.runtime
    selected size ordered childLifts childPreservation
    (named_bodies support issued extension (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
      root.port.header root.port.member selected)
    (fun _ fault => SelectedCompilationStageRawDirectSource.requirements_safe root.chain
      root.runtimeLedger.idsUnique root.port.evidence.produces fault)
    typed environments heaps locals agrees actualTyped initialState admitted raw

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
/-! The ordinary Source trace determines the induction grade. Each real body
uses strictly smaller ordinary traces; independently measured staged prefixes
supply the reached physical state through the closed preservation family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open SelectedCompilationPhysicalProgramSupport (Support functions stages)
open SelectedCompilationStageLiftBounds (LiftsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include issued extension in
/-- Every original selected expression either preserves its ordinary outcome
and heap or reaches a genuine earlier stage rejection at its exact heap. -/
theorem lifts_roots (size : Nat) :
    LiftsRootsAt (headers := headers) (keys := keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) size := by
  induction size using Nat.strongRecOn with
  | ind budget children =>
    intro context invocation scope expression lowered root owner keyPhysical
    cases root.support with
    | ordinary actual =>
      exact SelectedCompilationStageOrdinaryRootLifting.lifts
        support issued extension actual owner keyPhysical budget children
    | coercedDirect actual =>
      exact SelectedCompilationStageCoercedRootLifting.lifts
        support issued extension actual owner keyPhysical budget children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
end
