import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge

/-! Actual projected assignment phases share measured expression and sequence
contracts. Compatibility is a proof-only observer of the original Entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition

def legacyProtocol (guarded : ProtectedExpressionMeaning.Entry) : Protocol Unit where
  State index := PLift (guarded index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

def legacyTransport {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) : AdministrativeTransport (legacyProtocol guarded) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨transport.extend state.down maps worlds frame metadata⟩
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => trivial
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {entry : ProtectedExpressionMeaning.Entry}

/-- Only the old observer derives its lifted post through proved effects. -/
theorem legacy_preserves (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry) :
    PreservesAt (legacyProtocol entry) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_reflects (transport : ProtectedExpressionMeaning.Transport entry) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults entry) :
    ReflectsAt (legacyProtocol entry) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
