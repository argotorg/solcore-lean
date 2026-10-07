import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState

/-! Caller protocols expose the same actual full pool, and wrap an actual
returned pool only at the unchanged caller scope and canonical environment.
Record equality prevents replacement of any reached row or ordered history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A concrete caller wrapper changes neither its full pool nor records. Its
return operation wraps the actual post at the original scope/canonical only. -/
structure Carrier (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) where
  pool : ∀ {index}, caller.State index → State headers keys index
  records_eq : ∀ {index} (state : caller.State index), caller.records state = records (pool state)
  related : ∀ {initial reached} {first : caller.State initial} {last : caller.State reached},
    caller.Relates first last → Relates (pool first) (pool last)
  of_pool : ∀ {index} (_initial : caller.State index) {mapping world heap store},
    State headers keys (index.extend mapping world heap store) → caller.State (index.extend mapping world heap store)
  pool_of_pool : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)), pool (of_pool initial reached) = reached
  return_related : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)),
    Relates (pool initial) reached → caller.Relates initial (of_pool initial reached)

def base : Carrier (headers := headers) (protocol headers keys) where
  pool := fun state => state
  records_eq := fun _ => rfl
  related := fun related => related
  of_pool := fun {_index} _initial {_mapping _world _heap _store} reached => reached
  pool_of_pool := fun {_index} _initial {_mapping _world _heap _store} _reached => rfl
  return_related := fun {_index} _initial {_mapping _world _heap _store} _reached related => related

/-- Canonical slots come from this caller's original authentic packet. The
selected closure's captured slots belong to a separate body protocol. -/
def canonical (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) :
    Carrier (headers := headers) (argumentProtocol (headers := headers) owner callerPrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  of_pool := fun {_index} initial {_mapping _world _heap _store} reached => ⟨reached, initial.property⟩
  pool_of_pool := fun {_index} _initial {_mapping _world _heap _store} _reached => rfl
  return_related := fun {_index} _initial {_mapping _world _heap _store} _reached related => related

/-- Returning wraps the same ordered records at every row, including duplicates. -/
theorem Carrier.returned_records {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) caller)
    {index : ProtectedStateTransition.Index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)) :
    caller.records (carrier.of_pool initial reached) = records reached :=
  (carrier.records_eq _).trans (congrArg (fun state => records state) (carrier.pool_of_pool initial reached))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
