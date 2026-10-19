import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Lexical authority retains each actual generalized declaration's complete
compiler binding and native row. Transport requires a concrete effect on that
row; administrative preservation alone does not preserve mapped payloads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts

variable {definitions : DataEnvironment} {instances : InstanceModel definitions}

private theorem located_same {function binding lexical location mapping world heap store nextMap nextWorld after finalStore}
    (located : Located instances function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (read : finalStore.read? located.target = some (.inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value located.values))) :
    ∃ next : Located instances function binding lexical location nextMap nextWorld after finalStore,
      next.values = located.values := by
  obtain ⟨cell, sourceRead, _, descriptor⟩ := metadata location located.cell located.sourceRead
  have extendRows : ∀ {candidates values},
      SourceCoreLocalPolymorphism.ProductBundle.Pointwise
        (instances.Represents mapping world function binding lexical) candidates values →
      SourceCoreLocalPolymorphism.ProductBundle.Pointwise
        (instances.Represents nextMap nextWorld function binding lexical) candidates values := by
    intro candidates values rows
    induction rows with
    | nil => exact .nil
    | cons head _ ih => exact .cons (instances.extend head maps worlds) ih
  have rows := extendRows located.rows
  exact ⟨⟨located.attachment, cell, sourceRead, descriptor.trans located.descriptor,
    located.target, ⟨maps.lookup located.reference.mapped, worlds.lookup located.reference.typed⟩,
    located.values, rows, read⟩, rfl⟩

structure Effect (instances : InstanceModel definitions)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (nextMap : LocationMap) (nextWorld : StoreTyping) (after : Dynamic.Heap) (finalStore : Store) : Prop where
  metadata : Dynamic.HeapMetadataExtend heap after
  maps : LocationMap.Extends mapping nextMap
  worlds : WorldExtends world nextWorld
  retains_values : ∀ {function binding lexical location}
    (located : Located instances function binding lexical location mapping world heap store),
    ∃ next : Located instances function binding lexical location nextMap nextWorld after finalStore,
      next.values = located.values

theorem Effect.retains {mapping world heap store nextMap nextWorld after finalStore}
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore)
    {function binding lexical location}
    (located : Located instances function binding lexical location mapping world heap store) :
    Nonempty (Located instances function binding lexical location nextMap nextWorld after finalStore) := by
  obtain ⟨next, _⟩ := effect.retains_values located
  exact ⟨next⟩

theorem Effect.refl (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :
    Effect instances mapping world heap store mapping world heap store :=
  ⟨.refl _, .refl _, .refl _, fun located => ⟨located, rfl⟩⟩

theorem Effect.trans {mapping middleMap finalMap : LocationMap} {world middleWorld finalWorld : StoreTyping}
    {heap middleHeap finalHeap : Dynamic.Heap} {store middleStore finalStore : Store}
    (first : Effect instances mapping world heap store middleMap middleWorld middleHeap middleStore)
    (second : Effect instances middleMap middleWorld middleHeap middleStore finalMap finalWorld finalHeap finalStore) :
    Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  refine ⟨first.metadata.trans second.metadata, first.maps.trans second.maps,
    first.worlds.trans second.worlds, ?_⟩
  intro function binding lexical location located
  obtain ⟨middle, sameMiddle⟩ := first.retains_values located
  obtain ⟨last, sameLast⟩ := second.retains_values middle
  exact ⟨last, sameLast.trans sameMiddle⟩

theorem Effect.append {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
    {heap after : Dynamic.Heap} (store suffix : Store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    Effect instances mapping world heap store nextMap nextWorld after (store ++ suffix) := by
  refine ⟨metadata, maps, worlds, ?_⟩
  intro function binding lexical location located
  apply located_same located metadata maps worlds
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp located.nativeRead).1).trans located.nativeRead

theorem Effect.set_unmapped {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} (store : Store) {target : Core.Location}
    (value : Core.Value) (unmapped : target ∉ mapping) :
    Effect instances mapping world heap store mapping world heap (store.set target value) := by
  refine ⟨.refl _, .refl _, .refl _, ?_⟩
  intro function binding lexical location located
  have different : target ≠ located.target := by
    intro same
    exact unmapped (same.symm ▸ List.mem_of_getElem? located.reference.mapped)
  apply located_same located (.refl _) (.refl _) (.refl _)
  simpa [Store.read?, different] using located.nativeRead

theorem Effect.write_ordinary {mapping : LocationMap} {world : StoreTyping}
    {heap after : Dynamic.Heap} {store finalStore : Store}
    (injective : LocationMap.Injective mapping)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {target : Core.Location} {payload : Core.Ty}
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none)
    (reference : ReferenceRepresents mapping world location target payload)
    {sourceValue : Option Dynamic.Value} {nativeValue : Core.Value}
    (written : Dynamic.Heap.Writes heap location sourceValue after)
    (nativeWritten : store.write? target nativeValue = some finalStore) :
    Effect instances mapping world heap store mapping world after finalStore := by
  refine ⟨.of_write written, .refl _, .refl _, ?_⟩
  intro function binding lexical descriptorLocation located
  have different : descriptorLocation ≠ location := by
    intro same
    subst location
    have cells := located.sourceRead.functional read
    have descriptors := congrArg Dynamic.Cell.generalized cells
    rw [located.descriptor, ordinary] at descriptors
    cases descriptors
  have nativeDifferent : located.target ≠ target := by
    intro same
    have indices := injective (same ▸ located.reference.mapped) reference.mapped
    apply different
    cases descriptorLocation
    cases location
    exact congrArg Dynamic.Location.mk indices
  apply located_same located (.of_write written) (.refl _) (.refl _)
  exact (Store.write?_preserves_other nativeWritten nativeDifferent).trans located.nativeRead

inductive Entry (instances : InstanceModel definitions) (caller : SourceCoreLocalPolymorphism.Key)
    (active : Substitution) (id : Resolved.LocalId) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  | ordinary {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
      (descriptor : cell.generalized = none) :
      Entry instances caller active id location mapping world heap store
  | generalized {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution} (owner : binding.caller = caller) (binder : binding.binder.id = id)
      (context : ContextExtension lexical active)
      (located : Nonempty (Located instances function binding lexical location mapping world heap store)) :
      Entry instances caller active id location mapping world heap store

inductive At (instances : InstanceModel definitions) (caller : SourceCoreLocalPolymorphism.Key)
    (active : Substitution) (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :
    Dynamic.Environment → Prop where
  | nil : At instances caller active mapping world heap store []
  | cons {id : Resolved.LocalId} {location : Dynamic.Location} {rest : Dynamic.Environment}
      (head : Entry instances caller active id location mapping world heap store)
      (tail : At instances caller active mapping world heap store rest) :
      At instances caller active mapping world heap store ((id, location) :: rest)

theorem Entry.transport {caller active id location mapping world heap store nextMap nextWorld after finalStore}
    (entry : Entry instances caller active id location mapping world heap store)
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore) :
    Entry instances caller active id location nextMap nextWorld after finalStore := by
  cases entry with
  | ordinary read descriptor =>
    obtain ⟨cell, updated, _, same⟩ := effect.metadata _ _ read
    exact .ordinary updated (same.trans descriptor)
  | generalized owner binder context located =>
    obtain ⟨located⟩ := located
    exact .generalized owner binder context (effect.retains located)

theorem At.transport {caller active mapping world heap store nextMap nextWorld after finalStore environment}
    (authority : At instances caller active mapping world heap store environment)
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore) :
    At instances caller active nextMap nextWorld after finalStore environment := by
  induction authority with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.transport effect) ih

theorem At.lookup {caller active mapping world heap store environment id location}
    (authority : At instances caller active mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location) :
    Entry instances caller active id location mapping world heap store := by
  induction authority with
  | nil => cases lookup
  | cons head _ ih =>
    cases lookup with
    | head => exact head
    | tail _ next => exact ih next

theorem At.generalized {caller active mapping world heap store environment id location cell function}
    (authority : At instances caller active mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function) :
    ∃ binding lexical, binding.caller = caller ∧ binding.binder.id = id ∧ ContextExtension lexical active ∧
      Nonempty (Located instances function binding lexical location mapping world heap store) := by
  cases authority.lookup lookup with
  | ordinary previous empty =>
    have same := read.functional previous
    rw [same, empty] at descriptor
    cases descriptor
  | generalized owner binder context located =>
    obtain ⟨located⟩ := located
    have same := read.functional located.sourceRead
    have functionEq := Option.some.inj (descriptor.symm.trans ((congrArg Dynamic.Cell.generalized same).trans located.descriptor))
    cases functionEq
    exact ⟨_, _, owner, binder, context, ⟨located⟩⟩

/-- Real monomorphic parameter cells supply the initial lexical authority.
Deep Source heap typing rules out a principal descriptor at such a cell. -/
theorem At.of_monomorphic {caller active mapping world heap store environment scope}
    {context : SourceSemantics.Context}
    (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ scope → scheme.quantified = []) :
    At instances caller active mapping world heap store environment := by
  induction agrees with
  | nil => exact .nil
  | @cons scope environment id scheme location cell read _ storage tail ih =>
    have next := ih (fun child childScheme member => monomorphic child childScheme (List.mem_cons_of_mem _ member))
    cases storage with
    | ordinary _ empty => exact .cons (.ordinary read empty) next
    | generalized descriptor _ binderScheme =>
      have principal := ((typed cell read.member).generalized_inv descriptor).2.code.polymorphic
      exact False.elim (principal (binderScheme ▸ monomorphic id scheme (by simp)))

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
