import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates

import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment

/-! Pointwise finite tuple correspondence consumes the original sequence trace
and original native children. The source cost reconstructed by reflection is
independent of its native cost. Ordered child effects retain the caller entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionTuples RecursiveNamedCallBounds RecursiveNamedBoundedContracts

variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {children : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults childSize) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installed trace
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ :=
    source_inv_at receipt.metadata receipt.form unique trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    ProtectedDataExpressionSequence.Stateful.preserves_bounded protocol (budget + 1) sequence
      (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
      environments heaps locals agrees actualTyped installed sourceTrace (by omega)
  obtain ⟨actualOutcome, actualPacked, payload⟩ := sequence_result represented
  have sameOutcome := actualPacked.functional packed
  subst outcome
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
    by simpa only [receipt.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata, transition⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installed evaluated
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨sequenceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    ProtectedDataExpressionSequence.Stateful.reflects_bounded protocol (budget + 1) sequence
      (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
      environments heaps locals agrees actualTyped installed evaluated (by omega)
  obtain ⟨outcome, packed, payload⟩ := sequence_result represented
  have trace := source_intro receipt.metadata receipt.form sourceTrace.sound packed
  obtain ⟨sourceSize, measured⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, measured,
    by simpa only [receipt.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata, transition⟩

end Stateful

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → PreservesAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_at functions program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size within unique
      (fun child bound => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning child bound))
      certified found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.reflects_at functions program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size within
      (fun child bound => ProtectedStatePlaceAssignment.legacy_reflects transport (meaning child bound))
      certified found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
