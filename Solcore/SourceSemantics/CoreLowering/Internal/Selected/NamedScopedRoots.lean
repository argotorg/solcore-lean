import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls

/-!
# Selected compilations: scoped named roots

Scoped bounds, collectors and evidence frames of named bodies, and the physical mixed scoped roots they use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedBounds
/-! Actual named parameter entry supplies the physical slots, current authority,
and original frame used by the existing scoped flow engine. Every expression
child is discharged by the strictly smaller mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open SelectedCompilationNamedScopedSupport (Support)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {receipt : Receipt header}
  (support : Support headers header stages receipt semanticFaults)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)


variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include support globals selected semantic faithful observations assignmentInterpretation in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet keyPhysical physical slots size finalContext bodyOutcome outcome after trace matched within
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
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
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
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at
      physicalBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions faithful observations extension rfl header.registered
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) faults size :=
          children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (by rw [stages.source selected]; exact header.unique)
      tree catalogSites semantic assignmentDiagnostics rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    (by rw [stages.source selected]; exact header.unique) sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated header.fellThrough header.escaped ξ
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, representedBody, finalHeaps,
    maps, worlds, frame, metadata, reached.base.val, related, ?_⟩
  · simpa only [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · cases bodyOutcome with
    | breaking environment => exact (controlClosed.1 environment rfl).elim
    | continuing environment => exact (controlClosed.2 environment rfl).elim
    | returned => exact ⟨post.rows, post.successful⟩
    | fallthrough => exact ⟨post.rows, post.successful⟩
    | fault failure => cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include support globals selected semantic functionTypes faithful observations assignmentInterpretation in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet keyPhysical physical slots size value finalStore completed within
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
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1)
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
  have runtime := support.certified.runtime
  have graph : OccurrenceGraphWellFormed invocation.source := by
    rw [stages.source selected]
    exact runtime.graph
  have bodyTrace := completed
  rw [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at
      physicalBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions functionTypes faithful observations extension rfl header.registered
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : ReflectsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages invocation
            (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) faults size :=
          children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      graph tree catalogSites semantic assignmentDiagnostics rfl shape originalTyping receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound header.fellThrough header.escaped ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  refine ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld,
    trace, represented.body_result, representedBody, finalHeaps, maps, worlds, frame, metadata,
    reached.base.val, related, ?_⟩
  cases bodyOutcome with
  | breaking environment => exact (controlClosed.1 environment rfl).elim
  | continuing environment => exact (controlClosed.2 environment rfl).elim
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
/-! The original checked named body supplies native typing of every actual
lexical child. Original Source syntax and binder context transport feed only
static expression factories, then the generic compiler traversal retains the
same accepted allocations and finish code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem tree
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericLexicalStatements.Syntax header.function.source expressionSyntax
      header.context true header.function.body header.function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source
      (TypedCertificate header.function.source certificates)
      header.context (parameterScope header) true header.function.body header.function.resultType header.output receipt.flow := by
  have body := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  rw [receipt.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  have retained := certified
  obtain ⟨_, certificate⟩ := retained
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime := runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual true
    (values := .initial compiled.compatible.checked)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_allocator prepared aligned)
    (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields header.context context →
      TypedCertificate header.function.source certificates context scope id lowered)
    (fun context _closed _residual _signatures scope fuel id node lowered declarations approved found typed accepted nativeType native fields =>
      ⟨node, found, typed, children context fields declarations approved found typed accepted native⟩)
    syntaxTree runtime.variables_closed runtime.residual_variables_open
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header)) declarations
    receipt.projection receipt.accepted flowTyped
  exact Tree.discharge_context extracted (.refl _)


include aligned in
/-- Child factories receive only original syntax/typing, actual callback
acceptance and native typing, at the context reached by real lexical binders. -/
theorem collected_of_imperative
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source expressionSyntax
      header.context (.statements true header.function.body) header.function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) (faults := faults) header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source expressionSyntax
      (TypedCertificate header.function.source certificates) compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  have body := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  rw [receipt.emitted] at body
  obtain ⟨nativeType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow body
  have retained := certified
  obtain ⟨_, certificate⟩ := retained
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime := runtime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.assignments prepared
  have unaryPolicy : CompatibleBitNotStatements.Policy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.unary prepared
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
    (expressionSyntax := expressionSyntax) (certificates := certificates) (LocalView.refl _)
    (by intro id member; cases member) header.unique
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared aligned)
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_allocator prepared aligned)
    assignments unaryPolicy operands unary
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_match prepared aligned) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.match_allocator prepared aligned)
    (SelectedCompilationHeaderFacts.hidden_fresh certified)
    ((CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm ▸ catalog)
    (header.valid.ledger.trans aligned.solved)
    (fun context fields scope fuel id node lowered declarations approved _reached found typed accepted nativeType native =>
      children context fields (scope := scope) (fuel := fuel) (id := id) (node := node)
        (lowered := lowered) declarations approved found typed accepted (nativeType := nativeType) native)
    syntaxTree rfl receipt.shape (.refl _) runtime.variables_closed runtime.residual_variables_open
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
    receipt.projection receipt.accepted flowTyped


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
/-! The actual prepared named row and selected Source scope determine the
complete caller dictionary at every lexical context. Local changes preserve
the nonlocal context fields; no terminal body or execution premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
open Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- The dictionary keeps the original prepared row; the ledger and signature
facts refer to the actual context reached inside that named body. -/
structure CallerAt (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (context : SourceSemantics.Context) (child : Staging.Recursive.Scope) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized
  signatures : context.signatures = compiled.sourceProgram.signatures
  ledger : context.solvedRequirements = actual.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ actual.named.specialized.assumptions → goal ∈ context.assumptions
  unique : RequirementIdsUnique context
  dictionary : child.evidence = prepared.view.evidence

private theorem reindex_view {left right : SourceSpecialization.SpecializedFunction}
    (same : left = right) (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled left) :
    (same ▸ prepared).view = prepared.view := by
  cases same
  rfl

/-- Header preparation fixes the complete caller dictionary. Parameter entry
and subsequent lexical context changes preserve its assumptions and ledger. -/
def of_selected
    (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt actual instantiation header)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields header.context context)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    CallerAt actual context child := by
  let prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized :=
    actual.same.symm ▸ actual
  have view : prepared.view = actual.view := reindex_view _ _
  have parameters := RecursiveNamedInitialContextValidity.mono_fields header.extended
  refine ⟨prepared, ?_, fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved), ?_, ?_, ?_⟩
  · rw [fields.signatures, parameters.signatures, aligned.function]
    rfl
  · intro goal member
    rw [fields.assumptions, parameters.assumptions, aligned.function]
    exact member
  · simpa only [RequirementIdsUnique, fields.solvedRequirements] using
      (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
  · rw [stages.evidence selected, aligned.function, view]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedRoots
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
/-! The accepted named scoped compiler action issues physical mixed roots at
each reached lexical context. Exact header slots cover reached declarations;
full method cache slots remain the responsibility of the physical state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- Static child receipts are assembled into the same named branching support
consumed by the numeric body theorem. Source and native execution are absent
from the factory's premises. -/
def of_imperative_compiler
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {semanticFaults : FunctionCalls.FaultRep}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw semanticFaults operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → semanticFaults (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root))
    (stages : Staging.Recursive.Registry)
    {expressionSyntax : ExpressionId → Prop}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source expressionSyntax
      header.context (.statements true header.function.body) header.function.resultType)
    (children : ∀ child, stages.Closure header.function child →
      ∀ context, Dynamic.RuntimeContextFields header.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope context →
      expressionSyntax id → header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source context id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
        lowered.expression nativeType compiled.indexed.layouts.definitions →
      SelectedCompilationNamedScopedSupport.Certificate
        headers stages semanticFaults context child scope id lowered) :
    SelectedCompilationNamedScopedSupport.Support
      headers header stages receipt semanticFaults := by
  refine ⟨certified,
    RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared,
    RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared,
    PreparedAssignmentDiagnosticProducers.named prepared diagnostic aligned, ?_⟩
  intro child selected
  rw [stages.source selected]
  exact ⟨expressionSyntax, SelectedCompilationNamedBranchingCollectors.collected_of_imperative prepared aligned ready certified bodies.signatures member receipt operands unary syntaxTree (children child selected)⟩


include aligned in
/-- The actual prepared Header, per-site slots and source metadata issue
all mixed children without exposing a child execution premise. -/
def of_actual_with_catalog
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {directSites : DeclarationInstantiation → Prop}
    (supported : ∀ instantiation, directSites instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source directSites)
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
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    SelectedCompilationNamedScopedSupport.Support
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  have operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared site assignment.target.root operator) := by
    intro site assignment operator rhs origin profile
    obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
      prepared diagnostic aligned
    exact PreparedBranchingAssignmentDiagnostics.operands assignmentPrepared
      (fun _ _ represented => CallableIndexedOwnedPublicAssignmentDiagnostics.prepared_operands
        prepared diagnostic receiver represented) origin profile
  have unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs header.function.source site assignment →
      assignment.target.type = .word → CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.invalidUnaryOperand .bitNot)
        (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared site assignment.target.root) := by
    intro site assignment origin rawWord
    obtain ⟨first, assignmentPrepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
      prepared diagnostic aligned
    exact GenericAssignmentUnaryDiagnostics.prepared_unary_included assignmentPrepared
      (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.prepared_unary
        prepared diagnostic receiver represented) origin rawWord
  apply of_imperative_compiler prepared aligned ready diagnostic bodies certified member receipt operands
    unary
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := SelectedCompilationNamedPhysicalMixedScopedRoots.of_accepted_sites_with_catalog
    prepared aligned diagnostic receiver bodies certified supported metadata rows covered checked catalog methods actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact ⟨root, prefixEq⟩



end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedParentBounds
/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
Static named compiler provenance and strict expression coverage are inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (argumentsTyped : Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes)
  (argumentMetadata : Dynamic.HeapMetadataExtend calleeHeap argumentsHeap)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header argumentMap argumentWorld)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (certifiedAt : SelectedCompilationNamedArgumentRows.CertifiedAt (header := header) (function := function))
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
    (owner := owner) header capture identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include profile compiler prepared dispatch selected callerPrepared count runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt certifiedAt certified nativeType admitted in
private theorem arguments_at :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    SelectedCompilationNamedArgumentRows.accepted_rows sourceAt compiler certifiedAt
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    SelectedCompilationNamedArgumentRows.arguments_at sourceAt certifiedAt certified
      runtime admitted.heap argumentsTyped (calleeTyped.mono argumentMetadata) bundle physicalArity
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := values) functions owner (bridge.pool reached) header capture
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted owners runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult owner header capture sourceAt certifiedAt certified
  identity descriptorWord carrierEq nativeType sameLayouts member in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at bridge profile compiler prepared reached admitted dispatch selected callerPrepared count runtime
      calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt
      certifiedAt certified nativeType
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    SelectedCompilationNamedApplicationBounds.application_preserves
      functions owner (bridge.pool reached) header capture sourceAt sameLayouts member owners certified
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget children called within
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult owner header capture sourceAt certifiedAt certified
  identity descriptorWord carrierEq nativeType sameLayouts member namedPrepared aligned
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at bridge profile compiler prepared reached admitted dispatch selected callerPrepared count runtime
      calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt
      certifiedAt certified nativeType
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    SelectedCompilationNamedApplicationBounds.application_reflects
      functions owner (bridge.pool reached) header capture sourceAt
      namedPrepared aligned stagePrepared descriptor sameLayouts member certified admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget children application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedParentBounds
end
