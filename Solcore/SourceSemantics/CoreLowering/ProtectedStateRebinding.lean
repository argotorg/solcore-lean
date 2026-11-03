import Solcore.SourceSemantics.CoreLowering.ProtectedStateBindings

/-! A snapshot evaluates in the same lexical scope with other canonical cells.
Lexical bindings already remove and prepend one scope binder; repeating this
over the whole scope rebinds its canonical values while every slot past the
scope stays fixed. Administrative transitions are the propositional part of an
administrative transport. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap
universe u v

variable {Records : Type v} (protocol : Protocol.{u, v} Records)

/-- Every witness reaches each administrative extension of its index. -/
def AdministrativeTransitions : Prop :=
  ∀ {initial : Index} (_state : protocol.State initial) {mapping world heap store},
    LocationMap.Extends initial.mapping mapping → WorldExtends initial.world world →
    AdministrativePreserved initial.mapping initial.store mapping store →
    Dynamic.HeapMetadataExtend initial.heap heap →
    Transition protocol _state (initial.extend mapping world heap store)

theorem AdministrativeTransport.transitions (transport : AdministrativeTransport protocol) :
    AdministrativeTransitions protocol := by
  intro _ state _ _ _ _ maps worlds frame metadata
  exact AdministrativeTransport.transition protocol transport state maps worlds frame metadata

variable {protocol} (bindings : Bindings protocol)

include bindings in
/-- The scope binders are restored from the head and prepended again with the
new canonical values. -/
theorem Bindings.rebind :
    ∀ {index : Index} (state : protocol.State index) (canonical : Environment),
      index.scope.length ≤ index.canonical.length → index.scope.length ≤ canonical.length →
      (∀ slot, index.scope.length ≤ slot → canonical[slot]? = index.canonical[slot]?) →
      Transition protocol state { index with canonical := canonical } := by
  intro index
  obtain ⟨scope, mapping, world, heap, store, current⟩ := index
  induction scope generalizing current with
  | nil =>
    intro state canonical _ _ slots
    have same : canonical = current := List.ext_getElem? (fun slot => slots slot (Nat.zero_le _))
    subst same
    exact Transition.refl protocol state
  | cons head rest ih =>
    intro state canonical currentLength canonicalLength slots
    obtain ⟨id, type⟩ := head
    cases current with
    | nil => simp at currentLength
    | cons value tail =>
      cases canonical with
      | nil => simp at canonicalLength
      | cons replacement tail' =>
        have restored := bindings.restore_transition
          (index := ⟨rest, mapping, world, heap, store, tail⟩) (id := id) (type := type) (value := value) state
        refine Transition.then protocol restored (fun middle _ => ?_)
        have rebound := ih tail middle tail' (by simpa using currentLength) (by simpa using canonicalLength)
          (fun slot above => by
            dsimp only at above
            simpa using slots (slot + 1) (by dsimp only; simp only [List.length_cons]; omega))
        exact Transition.then protocol rebound (fun last _ => bindings.prepend_transition last id type replacement)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
