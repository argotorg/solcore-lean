import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter

/-! Static named lexical support retains each child at its actual context
and scope. A recursive expression or ordinary lambda producer is used through
the same protected lexical state; no body law belongs to the static packet. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedNamedLexicalReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Formation stores only the actual compiler Site and original Source facts.
Runtime captures are obtained later from the real lexical input packet. -/
inductive Certificate (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop where
  | recursive (root : RootAt compiled context invocation scope id lowered semanticFaults)
  | formation
      (actual : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
        header context invocation.evidence scope id lowered)
      (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
      (covers : invocation.evidence.Covers context)

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
    GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source
      (TypedCertificate child.source (fun context => Certificate header bodyRegistry semanticFaults context child))
      header.context (parameterScope header) true header.function.body header.function.resultType header.output receipt.flow

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
theorem preserves (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet size finalContext bodyOutcome outcome after trace matched within
  have packet := packet (support.zero owner) globals
  let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨initial, packet⟩
  have nestedAdmitted : Admission (nestedBridge owner) header.context wrapped :=
    ⟨admitted.heap, admitted.rows⟩
  have tree := support.tree invocation selected
  rw [layouts] at tree
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape invocation.source header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [globals, parameterScope] using packet.reference
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalPreservation.preserves
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      functions rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => preserves_children support globals profile selected children owner context within)
      (by rw [stages.source selected]; exact header.unique)
      tree rfl shape receipt.projection within environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted trace
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated header.fellThrough header.escaped ξ
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, representedBody, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related, ?_⟩
  · simpa only [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody
  · cases bodyOutcome with
    | breaking environment => exact (represented.noEscapedControl.1 environment rfl).elim
    | continuing environment => exact (represented.noEscapedControl.2 environment rfl).elim
    | returned => exact ⟨post.rows, post.successful⟩
    | fallthrough => exact ⟨post.rows, post.successful⟩
    | fault failure => cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include support globals selected in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects (layouts : header.layouts = compiled.indexed.layouts) {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped initial admitted owner packet size value finalStore completed within
  have packet := packet (support.zero owner) globals
  let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State
      ⟨parameterScope header, mapping, world, before, store, canonical⟩ := ⟨initial, packet⟩
  have nestedAdmitted : Admission (nestedBridge owner) header.context wrapped :=
    ⟨admitted.heap, admitted.rows⟩
  have tree := support.tree invocation selected
  rw [layouts] at tree
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape invocation.source header.function.body := by
    rw [stages.source selected]
    exact receipt.shape
  have reference : canonical[(parameterScope header).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [globals, parameterScope] using packet.reference
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position packet.carried
  have bodyTrace := completed
  rw [receipt.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFlow.reflects
      (nestedBridge owner) (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
      functions rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => reflects_children support globals profile selected children owner context within)
      tree rfl shape receipt.projection (Nat.le_of_lt strict) environments heaps locals agrees actualTyped reference read unmapped
      wrapped conditioned nestedAdmitted flowTrace
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound header.fellThrough header.escaped ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  refine ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld,
    trace, represented.body_result, representedBody, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, ?_⟩
  cases bodyOutcome with
  | breaking environment => exact (represented.noEscapedControl.1 environment rfl).elim
  | continuing environment => exact (represented.noEscapedControl.2 environment rfl).elim
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
