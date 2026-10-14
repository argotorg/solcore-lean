import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! Actual named parameter entry supplies the physical slots, current authority,
and original frame used by the existing scoped flow engine. Every expression
child is discharged by the strictly smaller mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport (Support)
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
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include support globals selected in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.PreservesRootsAt
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
  have catalogSites := collected.sites receiving semanticFaults
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape invocation.source true header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [canonical, globals, parameterScope] using packet.reference
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    RecursiveNamedHeaderSourceTyping.statements header support.wellFormed
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
      functions extension rfl header.registered
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
      tree catalogSites rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
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

include support globals selected in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds.ReflectsRootsAt
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
  have catalogSites := collected.sites receiving semanticFaults
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape invocation.source true header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [canonical, globals, parameterScope] using packet.reference
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    RecursiveNamedHeaderSourceTyping.statements header support.wellFormed
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements invocation.source header.context header.function.body :=
    ⟨_, _, _, sourceTyped⟩
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header support.wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
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
      functions extension rfl header.registered
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
      graph tree catalogSites rfl shape originalTyping receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedBounds
