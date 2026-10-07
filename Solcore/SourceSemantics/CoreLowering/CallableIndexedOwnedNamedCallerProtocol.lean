import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState

/-! A stronger caller returns the same actual reached pool using the real
map, world, administrative and Source heap receipts. Its own static admission
and canonical slots stay separate from the selected named body's admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Slots are authentic static caller receipts. Returning accepts the actual
post pool and every original preservation receipt, so stronger caller facts
need never be inferred from a bare pool. -/
structure Carrier (slots : ProtectedStateTransition.Index → Prop)
    (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) where
  pool : ∀ {index}, caller.State index → State headers keys index
  records_eq : ∀ {index} (state : caller.State index), caller.records state = records (pool state)
  related : ∀ {initial reached} {first : caller.State initial} {last : caller.State reached},
    caller.Relates first last → Relates (pool first) (pool last)
  slots : ∀ {index}, caller.State index → slots index
  restore : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)),
    LocationMap.Extends index.mapping mapping → WorldExtends index.world world →
    AdministrativePreserved index.mapping index.store mapping store →
    Dynamic.HeapMetadataExtend index.heap heap → Relates (pool initial) reached →
    ∃ returned : caller.State (index.extend mapping world heap store),
      pool returned = reached ∧ caller.Relates initial returned

/-- The returned wrapper observes exactly the actual ordered reached records,
including repeated snapshots. -/
theorem Carrier.returned_records {slots : ProtectedStateTransition.Index → Prop}
    {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) slots caller)
    {index : ProtectedStateTransition.Index} {mapping world heap store}
    {returned : caller.State (index.extend mapping world heap store)}
    {reached : State headers keys (index.extend mapping world heap store)}
    (same : carrier.pool returned = reached) : caller.records returned = records reached :=
  (carrier.records_eq returned).trans (congrArg (fun state => records state) same)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
