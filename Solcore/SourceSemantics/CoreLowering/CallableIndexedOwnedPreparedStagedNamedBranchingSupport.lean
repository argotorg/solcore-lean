import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites

/-! Static named branching support retains each child at its actual context
and scope. A recursive expression or ordinary lambda producer is used through
the same protected state; branches and finite while loops restore outer bindings
while retaining their actual heap and assignment effects.
No body law belongs to the static packet. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

open CallableIndexedOwnedPreparedStagedNamedLexicalSupport (Certificate)

structure Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate header bodyRegistry semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {receipt : Receipt header}
  (support : Support headers keys bodyRegistry header stages receipt semanticFaults)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "nestedBridge" owner => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner header

include support globals selected in
/-- The exact pool result is wrapped with its retained nested packet after
recursive children, while formation consumes that same packet directly. -/
theorem preserves_children {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (owner : OwnedKey keys) (context : SourceSemantics.Context)
    {size : Nat} (within : size < budget) :
    PreservesAt (nestedBridge owner) context model stages invocation
      (Certificate header bodyRegistry semanticFaults context invocation) faults size := by
  intro scope id lowered certified
  cases certified with
  | recursive root =>
      intro node found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
        environments heaps locals agrees actualTyped initial admitted trace
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
          frame, metadata, reached, related, post⟩ :=
        children size within root ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees actualTyped
          initial.val ⟨admitted.heap, admitted.rows⟩ trace
      let next : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
          ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ :=
        ⟨reached, initial.property.after owner header reached frame⟩
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, next, related, ?_⟩
      cases outcome with
      | value => exact ⟨post.rows, post.successful⟩
      | fault failure => cases failure with
        | semantic => exact ⟨post.rows, post.successful⟩
        | stage => exact post
  | formation actual runtime covers =>
      exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.preserves
        header owner context invocation profile support.complete globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (support.zero owner)
        (by rw [stages.source selected]; exact header.agreement.source)
        (by rw [stages.source selected]; exact header.unique)
        support.wellFormed runtime covers faults size ⟨actual⟩

include support globals selected in
theorem reflects_children {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (owner : OwnedKey keys) (context : SourceSemantics.Context)
    {size : Nat} (within : size < budget) :
    ReflectsAt (nestedBridge owner) context model stages invocation
      (Certificate header bodyRegistry semanticFaults context invocation) faults size := by
  intro scope id lowered certified
  cases certified with
  | recursive root =>
      intro node found typed mapping world administrative environment canonical actual actualContext before store ξ value finalStore
        environments heaps locals agrees actualTyped initial admitted completed
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
          frame, metadata, reached, related, post⟩ :=
        children size within root ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees actualTyped
          initial.val ⟨admitted.heap, admitted.rows⟩ completed
      let next : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
          ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ :=
        ⟨reached, initial.property.after owner header reached frame⟩
      refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, next, related, ?_⟩
      cases outcome with
      | value => exact ⟨post.rows, post.successful⟩
      | fault failure => cases failure with
        | semantic => exact ⟨post.rows, post.successful⟩
        | stage => exact post
  | formation actual runtime covers =>
      exact CallableIndexedOwnedPreparedStagedLambdaFormationHeads.reflects
        header owner context invocation profile support.complete globals
        (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (support.zero owner)
        (by rw [stages.source selected]; exact header.agreement.source)
        support.wellFormed runtime covers faults size ⟨actual⟩


include support globals selected in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet size finalContext bodyOutcome outcome after trace matched within
  have originalPacket := packet (support.zero owner) globals
  have prefixAgreement := CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix.entry_prefix
    header owner initial originalPacket support.complete environments
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
  let canonical := canonical.take ((parameterScope header).length +
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨initial, packet⟩
  have nestedAdmitted : Admission (nestedBridge owner) header.context wrapped :=
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
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
      functions extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => preserves_children support globals profile selected children owner context within)
      (by rw [stages.source selected]; exact header.unique)
      tree catalogSites rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated header.fellThrough header.escaped ξ
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, representedBody, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related, ?_⟩
  · simpa only [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · cases bodyOutcome with
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
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet size value finalStore completed within
  have originalPacket := packet (support.zero owner) globals
  have prefixAgreement := CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix.entry_prefix
    header owner initial originalPacket support.complete environments
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
  let canonical := canonical.take ((parameterScope header).length +
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header).length)
  let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨initial, packet⟩
  have nestedAdmitted : Admission (nestedBridge owner) header.context wrapped :=
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
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
      functions extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => reflects_children support globals profile selected children owner context within)
      graph tree catalogSites rfl shape originalTyping receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function receipt.projection represented
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound header.fellThrough header.escaped ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  refine ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld,
    trace, represented.body_result, representedBody, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, ?_⟩
  cases bodyOutcome with
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingSupport
