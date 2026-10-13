import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds

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
