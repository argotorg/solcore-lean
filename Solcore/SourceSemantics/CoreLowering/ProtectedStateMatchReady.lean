import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchPrefix

/-! Match readiness is established at the actual combined prefix post. The
pure Source hidden and pattern allocations justify its heap; no intermediate
protocol witness is assumed. Restoration consumes the actual later body post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (readiness : Readiness protocol) (source : TypedSource)

structure PrefixTransfers where
  hidden : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {value : Dynamic.Value} {location : Dynamic.Location},
    readiness.Ready context first → readiness.ValueFacts context initial.heap value type →
    Dynamic.Heap.Allocates initial.heap type (some value) location reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready context last
  arm : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context armContext : SourceSemantics.Context} {control : ControlContext} {resolution : MatchResolution}
    {type : TypeSystem.Ty} {caseFacts : List BodyFacts} {value : Dynamic.Value} {hidden : Dynamic.Heap}
    {location : Dynamic.Location} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    {environment armEnvironment : Dynamic.Environment},
    readiness.Ready context first → readiness.ValueFacts context initial.heap value type →
    Dynamic.Heap.Allocates initial.heap type (some value) location hidden →
    MatchCasesHaveType source control context type resolution.cases caseFacts →
    Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings) →
    BindersExtend source.owner context (bindings.map Prod.fst) armContext →
    Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready armContext last
  restore_arm : ∀ {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder},
    BindersExtend source.owner context binders armContext →
    ∀ {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩),
      readiness.Ready armContext state → readiness.Ready context (returnTo.restore state)
  restore_parent : ∀ {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context},
    ∀ {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩),
      readiness.Ready context state → readiness.Ready context (returnTo.restore state)

variable {protocol readiness source}

theorem PrefixTransfers.trivial (protocol : Protocol.{u, v} Records) (source : TypedSource) :
    PrefixTransfers protocol (Readiness.trivial protocol) source where
  hidden := by intros; exact True.intro
  arm := by intros; exact True.intro
  restore_arm := by intros; exact True.intro
  restore_parent := by intros; exact True.intro

theorem PrefixTransfers.post_arm (transfers : PrefixTransfers protocol readiness source)
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend source.owner context binders armContext)
    {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    {outcome : Dynamic.ControlOutcome} (post : PostReady readiness armContext outcome state) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) (returnTo.restore state) := by
  cases outcome with
  | fault => exact readiness.fault_after state (returnTo.restore state) post (AdministrativePreserved.refl _ _)
  | fallthrough | returned | breaking | continuing => exact transfers.restore_arm returnTo extended state post

theorem PrefixTransfers.post_parent (transfers : PrefixTransfers protocol readiness source)
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context}
    {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    {outcome : Dynamic.ControlOutcome} (post : PostReady readiness context outcome state) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) (returnTo.restore state) := by
  cases outcome with
  | fault => exact readiness.fault_after state (returnTo.restore state) post (AdministrativePreserved.refl _ _)
  | fallthrough | returned | breaking | continuing => exact transfers.restore_parent returnTo state post

end Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
