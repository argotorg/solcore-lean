import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
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
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds

/-! Canonical direct and index children use the actual named parameter packet
through the existing scoped flow engine. Lexical allocation, finite loops and
assignments retain the genuine pool, global slots and complete record history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalNamedBranchingSupport
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

open CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport (Certificate NamedSupport)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {receipt : Receipt header}
  (support : NamedSupport headers keys bodyRegistry header stages receipt semanticFaults)
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
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size)
    (owner : OwnedKey keys) (context : SourceSemantics.Context)
    {size : Nat} (within : size < budget) :
    PreservesAt (nestedBridge owner) context model stages invocation
      (Certificate headers header bodyRegistry semanticFaults context invocation) faults size := by
  intro scope id lowered certified
  induction certified generalizing size with
  | legacy actual =>
    cases actual with
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
  | canonical root samePrefix =>
    exact canonicalChildren size within root owner
      (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.nestedCaller
        owner header root.compilation.administrativePrefix samePrefix) ⟨rfl, rfl, rfl⟩
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
    have childMeaning : PreservesBelow (nestedBridge owner) context model stages invocation
        (Point scope inner code) faults size := by
      intro childSize smaller current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact ih (Nat.lt_trans smaller within)
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves (nestedBridge owner)
      (by rw [stages.source selected]; exact header.unique) size childMeaning size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes runtime covers actual sequence children ih =>
    have childMeaning : PreservesBelow (nestedBridge owner) context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) faults size := by
      intro childSize smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member (Nat.lt_trans smaller within)
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves (nestedBridge owner)
      functions faults (by rw [stages.source selected]; exact header.unique)
      support.wellFormed runtime covers size childMeaning
      ⟨node, ids, types, codes, rfl, actual, sequence⟩


include support globals selected in
theorem reflects_children {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size)
    (owner : OwnedKey keys) (context : SourceSemantics.Context)
    {size : Nat} (within : size < budget) :
    ReflectsAt (nestedBridge owner) context model stages invocation
      (Certificate headers header bodyRegistry semanticFaults context invocation) faults size := by
  intro scope id lowered certified
  induction certified generalizing size with
  | legacy actual =>
    cases actual with
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
  | canonical root samePrefix =>
    exact canonicalChildren size within root owner
      (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.nestedCaller
        owner header root.compilation.administrativePrefix samePrefix) ⟨rfl, rfl, rfl⟩
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
    have childMeaning : ReflectsAt (nestedBridge owner) context model stages invocation
        (Point scope inner code) faults size := by
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact ih within
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects (nestedBridge owner)
      (by rw [stages.source selected]; exact header.unique) size childMeaning
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes runtime covers actual sequence children ih =>
    have childMeaning : ReflectsBelow (nestedBridge owner) context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) faults (size + 1) := by
      intro childSize smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ smaller) within)
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects (nestedBridge owner)
      functions faults (by rw [stages.source selected]; exact header.unique)
      support.wellFormed runtime covers size childMeaning
      ⟨node, ids, types, codes, rfl, actual, sequence⟩



variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include support globals selected semantic in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
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
  have catalogSites := collected.sites receiving
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
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled)
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
      functions extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => preserves_children support globals profile selected children canonicalChildren owner context within)
      (by rw [stages.source selected]; exact header.unique)
      tree catalogSites semantic rfl shape originalTyping receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
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
    maps, worlds, frame, metadata, reached.val, related, ?_⟩
  · simpa only [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · cases bodyOutcome with
    | breaking environment => exact (controlClosed.1 environment rfl).elim
    | continuing environment => exact (controlClosed.2 environment rfl).elim
    | returned => exact ⟨post.rows, post.successful⟩
    | fallthrough => exact ⟨post.rows, post.successful⟩
    | fault failure => cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include support globals selected semantic in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
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
  have catalogSites := collected.sites receiving
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
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled)
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
      functions extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => reflects_children support globals profile selected children canonicalChildren owner context within)
      graph tree catalogSites semantic rfl shape originalTyping receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
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
    reached.val, related, ?_⟩
  cases bodyOutcome with
  | breaking environment => exact (controlClosed.1 environment rfl).elim
  | continuing environment => exact (controlClosed.2 environment rfl).elim
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalNamedBranchingSupport
