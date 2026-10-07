import Solcore.SourceSemantics.CoreLowering.ProtectedState

/-! Lexical binders reindex the concrete reached state. The source-visible
payload reference is prepended and later removed; heap and native store stay
fixed. Both operations preserve the complete record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference
universe u v

def Index.prepend (index : Index) (id : Resolved.LocalId) (type : Ty) (value : Value) : Index :=
  { index with scope := (id, type) :: index.scope, canonical := value :: index.canonical }

/-- These operations concern the actual canonical source binder. Hidden Core
slots continue to use the existing renaming and do not reindex this state. -/
structure Bindings {Records : Type v} (protocol : Protocol.{u, v} Records) where
  prepend : ∀ {index : Index} (_state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.State (index.prepend id type value)
  prepend_related : ∀ {index : Index} (state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.Relates state (prepend state id type value)
  prepend_records : ∀ {index : Index} (state : protocol.State index) (id : Resolved.LocalId)
    (type : Ty) (value : Value), protocol.records (prepend state id type value) = protocol.records state
  restore : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value},
    protocol.State (index.prepend id type value) → protocol.State index
  restore_related : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)), protocol.Relates state (restore state)
  restore_records : ∀ {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)), protocol.records (restore state) = protocol.records state

variable {Records : Type v} {protocol : Protocol.{u, v} Records} (bindings : Bindings protocol)

include bindings in
theorem Bindings.prepend_transition {index : Index} (state : protocol.State index)
    (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Transition protocol state (index.prepend id type value) :=
  ⟨bindings.prepend state id type value, bindings.prepend_related state id type value⟩

include bindings in
theorem Bindings.restore_transition {index : Index} {id : Resolved.LocalId} {type : Ty} {value : Value}
    (state : protocol.State (index.prepend id type value)) : Transition protocol state index :=
  ⟨bindings.restore state, bindings.restore_related state⟩

include bindings in
/-- Removing a binder consumes the child's reached witness, so any records
created inside the lexical suffix remain in the returned state. -/
theorem Bindings.restore_reached {initial reached : Index} (state : protocol.State initial)
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (transition : Transition protocol state (reached.prepend id type value)) :
    Transition protocol state reached := by
  obtain ⟨final, related⟩ := transition
  exact ⟨bindings.restore final, protocol.trans related (bindings.restore_related final)⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
