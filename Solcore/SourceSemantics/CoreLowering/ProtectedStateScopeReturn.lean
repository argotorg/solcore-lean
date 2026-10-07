import Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings

/-! A lexical prefix returns the actual reached state to its input scope and
canonical environment. The receipt applies after any later heap/store effects
and keeps the complete record observation. Its constructors use only the
identity operation and the proved concrete binder restoration interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference
universe u v

structure ReturnTo {Records : Type v} (protocol : Protocol.{u, v} Records)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (reachedScope : SourceCoreLocalCell.Scope) (reachedCanonical : Environment) where
  restore : ∀ {mapping world heap store},
    protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩ →
    protocol.State ⟨scope, mapping, world, heap, store, canonical⟩
  related : ∀ {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩),
    protocol.Relates reached (restore reached)
  records_eq : ∀ {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩),
    protocol.records (restore reached) = protocol.records reached

variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  {scope middleScope reachedScope : SourceCoreLocalCell.Scope}
  {canonical middleCanonical reachedCanonical : Environment}

def ReturnTo.refl (protocol : Protocol.{u, v} Records) (scope : SourceCoreLocalCell.Scope)
    (canonical : Environment) : ReturnTo protocol scope canonical scope canonical where
  restore reached := reached
  related reached := protocol.refl reached
  records_eq _ := rfl

/-- Compose concrete scope restoration without changing the actual effects. -/
def ReturnTo.then (first : ReturnTo protocol scope canonical middleScope middleCanonical)
    (last : ReturnTo protocol middleScope middleCanonical reachedScope reachedCanonical) :
    ReturnTo protocol scope canonical reachedScope reachedCanonical where
  restore reached := first.restore (last.restore reached)
  related reached := protocol.trans (last.related reached) (first.related (last.restore reached))
  records_eq reached := (first.records_eq (last.restore reached)).trans (last.records_eq reached)

/-- Remove one real source binder from any later reached state. -/
def ReturnTo.binding (bindings : Bindings protocol) (scope : SourceCoreLocalCell.Scope)
    (canonical : Environment) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    ReturnTo protocol scope canonical ((id, type) :: scope) (value :: canonical) where
  restore := fun {mapping world heap store} reached =>
    bindings.restore (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached
  related := fun {mapping world heap store} reached =>
    bindings.restore_related (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached
  records_eq := fun {mapping world heap store} reached =>
    bindings.restore_records (index := ⟨scope, mapping, world, heap, store, canonical⟩)
      (id := id) (type := type) (value := value) reached

theorem ReturnTo.transition (receipt : ReturnTo protocol scope canonical reachedScope reachedCanonical)
    {mapping world heap store}
    (reached : protocol.State ⟨reachedScope, mapping, world, heap, store, reachedCanonical⟩) :
    Transition protocol reached ⟨scope, mapping, world, heap, store, canonical⟩ :=
  ⟨receipt.restore reached, receipt.related reached⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
