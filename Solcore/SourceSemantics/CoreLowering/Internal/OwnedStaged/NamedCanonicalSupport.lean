import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.Staging.Internal.FaultCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedScopedPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds

/-!
# Staged bounds: named canonical support

Lexical, branching and recursive terminal support of named bodies, and the canonical scoped support and expression bounds they use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingSupport
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
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
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

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

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


include support globals selected semantic assignmentInterpretation in
/-- The original named body enters the same protected lexical engine and
returns the exact reached pool, including cells captured by its result. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults]
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
  have catalogSites := collected.sites receiving
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
  rw [← stages.source selected] at assignmentDiagnostics
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
      functions (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedContextualFunctionViews.observations profile) extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => preserves_children support globals profile selected children owner context within)
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

include support globals selected semantic assignmentInterpretation in
/-- Native completion is inverted through its real flow prefix and footer;
no selected final Source context is assumed. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults]
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
  have catalogSites := collected.sites receiving
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready
      (values := .initial compiled.compatible.checked) functions (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      header.function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
  rw [← stages.source selected] at assignmentDiagnostics
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
      functions (CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
      (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
      (CallableIndexedOwnedContextualFunctionViews.observations profile) extension rfl header.registered
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header model)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header model stable)
      (fun context size within => reflects_children support globals profile selected children owner context within)
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
    reached.val, related, ?_⟩
  cases bodyOutcome with
  | breaking environment => exact (controlClosed.1 environment rfl).elim
  | continuing environment => exact (controlClosed.2 environment rfl).elim
  | returned => exact ⟨post.rows, post.successful⟩
  | fallthrough => exact ⟨post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
/-! A named terminal's original compiler policy produces finite recursive
expression support. Actual Source typing, diagnostic issuance and selected
sidecars supply the call ports; no execution or payload representation is an
input. The original contextual callback keeps its own compiler budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (PolicyFor Syntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)

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
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source)
  (tree : Syntax header.function.source terminal.expression)
  {stages : Staging.Recursive.Registry}

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include metadata tree in
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
  have syntaxTree := CallableIndexedOwnedPreparedStagedCanonicalCallsReady.calls_syntax path
    (by simpa only [sameSource] using tree)
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.recipe_policy_for
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

include diagnostic receiver wellFormed metadata tree in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.RootAt compiled
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt } := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  have sourceEq := stages.source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.recipe_policy_for
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
  have childProfile : PolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, Syntax child.source id →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : Syntax child.source terminal.expression := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    calls_ready terminal metadata tree root sourceEq authority childTyped certificate
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  let support := CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.RootAt.of_compiled
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted ready rawType
    (header.valid.ledger.trans terminal.aligned.solved)
    (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed)
    wellFormed runtime
    (by rw [stages.evidence selected]; exact RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
        terminal.aligned receiver (by simpa only [sourceEq] using receipt) location)
  exact ⟨support, rfl, rfl⟩

include diagnostic receiver wellFormed metadata tree in
/-- Genuine root acceptance produces the finite certificate at every actual
selected scope. The returned support feeds the existing public body family. -/
theorem of_terminal
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (scopes : ∀ child, stages.Closure header.function child → SidecarAt terminal child) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header stages terminal faults) := by
  obtain ⟨fuel, root⟩ := policy_receipt terminal
  obtain ⟨root⟩ := root
  refine ⟨{ point := point, roots := ?_ }⟩
  intro child selected
  exact at_scope terminal diagnostic receiver wellFormed metadata tree root child selected (scopes child selected)

include diagnostic receiver wellFormed metadata tree in
/-- The actual named hook supplies its canonical sidecar. Genuine Source
origins and program typing identify every selected guard frame, without
excluding lambdas or other specializations of the same declaration. -/
theorem of_actual
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      header (RecursiveNamedPreparedStageScopes.registry actual) terminal faults) := by
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
  apply of_terminal terminal diagnostic receiver wellFormed metadata tree point
  intro child selected
  refine { sidecar := sidecar, issued := ?_, view := .inl canonicalSource, guards := ?_ }
  · simpa only [terminal.aligned.named] using issued
  · exact RecursiveNamedPreparedScopeCoherence.selected_frame actual
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
/-! General recursive expressions share the existing named scoped compiler
flow with legacy expressions and ordinary formation. Each canonical child
retains its actual compiler prefix; no runtime globals or body law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Existing recursive/formation certificates remain explicit alternatives.
The canonical branch retains only static root and compiler-prefix authority. -/
inductive Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | legacy {id lowered} (actual : CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
      header bodyRegistry semanticFaults context invocation scope id lowered) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id lowered
  | canonical {id lowered} (root : CanonicalRootAt compiled headers context invocation scope id lowered semanticFaults)
      («prefix» : root.compilation.administrativePrefix = 1) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id lowered
  | group {id node inner innerNode code}
      (metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked invocation.source id node code.type)
      (form : node.form = .group inner)
      (innerFound : invocation.source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Certificate headers header bodyRegistry semanticFaults context invocation scope inner code) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id code
  | tuple {id node ids types codes}
      (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
      (covers : invocation.evidence.Covers context)
      (actual : CompatibleExpressionTuples.Header (.initial compiled.compatible.checked) invocation.source id node ids types codes)
      (sequence : DataExpressionSequence.Tree invocation.source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Certificate headers header bodyRegistry semanticFaults context invocation scope child code) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id
        (SourceCoreCalls.packArguments codes)

/-- The same authentic branching receipt covers lexical bodies, branches and
finite loops. Collected retains its own compiler tree and catalog sites. -/
structure NamedSupport
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
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers header bodyRegistry semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds
/-! Mixed recursive expressions consume the same authentic nested packet in
named and ordinary closure bodies. Source identity comes from the selected
body's retained origin; no named invocation or child execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport (Certificate)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry}
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (globals : header.globals = compiled.indexed.base.globals.length)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope}
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source header.named)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "nestedBridge" owner => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner header

include complete zero wellFormed globals sameSource unique in
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
          header owner context invocation profile complete globals
          (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (zero owner)
          sameSource
          unique
          wellFormed runtime covers faults size ⟨actual⟩
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
      unique size childMeaning size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes runtime covers actual sequence children ih =>
    have childMeaning : PreservesBelow (nestedBridge owner) context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) faults size := by
      intro childSize smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member (Nat.lt_trans smaller within)
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves (nestedBridge owner)
      functions faults unique
      wellFormed runtime covers size childMeaning
      ⟨node, ids, types, codes, rfl, actual, sequence⟩
include complete zero wellFormed globals sameSource unique in
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
          header owner context invocation profile complete globals
          (RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers) (zero owner)
          sameSource
          wellFormed runtime covers faults size ⟨actual⟩
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
      unique size childMeaning
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes runtime covers actual sequence children ih =>
    have childMeaning : ReflectsBelow (nestedBridge owner) context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) faults (size + 1) := by
      intro childSize smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ smaller) within)
    intro actualNode
    exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects (nestedBridge owner)
      functions faults unique
      wellFormed runtime covers size childMeaning
      ⟨node, ids, types, codes, rfl, actual, sequence⟩



end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds
end
