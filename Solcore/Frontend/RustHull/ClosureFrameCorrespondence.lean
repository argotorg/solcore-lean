import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! Installed function and loop closures survive source computation. Source
locals cannot contain closures, so their writes cannot alias these cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def ClosuresPreserved (initial final : Core.Store) : Prop :=
  ∀ {location parameter result body environment},
    initial.read? location = some (.inRight .unit (.closure parameter result body environment)) →
    final.read? location = some (.inRight .unit (.closure parameter result body environment))

theorem ClosuresPreserved.refl (store : Core.Store) : ClosuresPreserved store store :=
  fun found => found

theorem ClosuresPreserved.trans {first middle last : Core.Store}
    (firstStep : ClosuresPreserved first middle) (secondStep : ClosuresPreserved middle last) :
    ClosuresPreserved first last := fun found => secondStep (firstStep found)

theorem ClosuresPreserved.append (store suffix : Core.Store) :
    ClosuresPreserved store (store ++ suffix) := by
  intro location parameter result body environment found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using found

theorem ClosuresPreserved.write {store updated : Core.Store}
    {world : World} {source : Semantics.Heap} (heap : HeapRel world source store)
    {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (entry : world[index]? = some (type, location))
    (written : store.write? location value = some updated) :
    ClosuresPreserved store updated := by
  intro retainedLocation parameter result body environment found
  have different : retainedLocation ≠ location := by
    intro same
    obtain ⟨sourceValue, targetValue, _, read, related⟩ := heap.cell index type location entry
    rw [same] at found
    have equal := Option.some.inj (read.symm.trans found)
    cases equal
    exact ValueRel.not_closure related
  rw [Core.Store.write?_preserves_other written different]
  exact found

theorem InstalledGlobals.preserved {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {initial final : Core.Store}
    (installed : InstalledGlobals codes locations environment initial)
    (preserved : ClosuresPreserved initial final) :
    InstalledGlobals codes locations environment final := by
  intro index code found
  exact preserved (installed index code found)

end Solcore.Frontend.RustHull.Correspondence
