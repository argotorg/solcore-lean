import Solcore.Frontend.RustHull.EffectEnvironmentCorrespondence
import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.RuntimeMemoryInitializationCorrespondence
import Solcore.Frontend.RustHull.RuntimeAssemblyCorrespondence

/-! The runtime references supplied by actual allocation line up with the
compiler's reversed frame scope. Unique slot names determine each cell lookup. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def effectSlotBinding (slot : EffectSlot) : Binding :=
  ⟨some (Effects.slotName slot.name), slot.type, false⟩

def effectSlotReference (slot : EffectSlot) : Core.Value := .cellRef slot.type slot.location

theorem EffectEnvironmentRel.of_slots (slots : List EffectSlot)
    (unique : (slots.map EffectSlot.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel slots (slots.map effectSlotBinding) Core.Renaming.id
      (slots.map effectSlotReference ++ caller) := by
  induction slots with
  | nil => exact .empty _ _ _
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      intro slot member binding index looked
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.map_cons, scope_lookup_cons, effectSlotBinding,
          beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at looked
        obtain ⟨rfl, rfl⟩ := looked
        rfl
      · have different : head.name ≠ slot.name := by
          intro same
          exact absent (List.mem_map.mpr ⟨slot, member, same.symm⟩)
        have names : Effects.slotName head.name ≠ Effects.slotName slot.name := by
          intro same
          exact different (by simpa [Effects.slotName] using same)
        simp only [List.map_cons, scope_lookup_cons, effectSlotBinding,
          Option.some_beq_some, beq_eq_false_iff_ne.mpr names, Bool.false_eq_true, ↓reduceIte] at looked
        cases previous : Scope.lookup (rest.map effectSlotBinding) (Effects.slotName slot.name) with
        | error error => simp only [previous] at looked; contradiction
        | ok pair =>
            rcases pair with ⟨oldBinding, oldIndex⟩
            simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
            obtain ⟨rfl, rfl⟩ := looked
            exact ih tailUnique slot member oldBinding oldIndex previous

/-- The exact value order unpacked by frameUnpack denotes every reserved slot.
Caller values may include the argument bundle and arbitrary captured closures. -/
theorem EffectEnvironmentRel.frame (slots : List EffectSlot)
    (unique : (slots.map EffectSlot.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel slots
      (AccountRuntime.frameScope (slots.map fun slot => (slot.name, slot.type))) Core.Renaming.id
      ((slots.map effectSlotReference).reverse ++ caller) := by
  have reversed := EffectEnvironmentRel.of_slots slots.reverse
    (by
      rw [List.map_reverse]
      exact List.pairwise_reverse.mpr (unique.imp (fun different => Ne.symm different))) caller
  intro slot member binding index looked
  have lookup : Scope.lookup (slots.reverse.map effectSlotBinding) (Effects.slotName slot.name) = .ok (binding, index) := by
    have same : AccountRuntime.frameScope (slots.map fun slot => (slot.name, slot.type)) = slots.reverse.map effectSlotBinding := by
      simp only [AccountRuntime.frameScope, List.map_reverse, List.map_map]
      rfl
    rw [← same]
    exact looked
  simpa only [List.map_reverse] using reversed slot (List.mem_reverse.mpr member) binding index lookup

def InitializedCell.effectSlot (cell : InitializedCell) : EffectSlot :=
  ⟨cell.name, cell.type, cell.location⟩

theorem initialized_environment (cells : List InitializedCell)
    (unique : (cells.map InitializedCell.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel (cells.map InitializedCell.effectSlot)
      (AccountRuntime.frameScope (cells.map fun cell => (cell.name, cell.type))) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ caller) := by
  have related := EffectEnvironmentRel.frame (cells.map InitializedCell.effectSlot)
    (by simpa only [List.map_map, Function.comp_def, InitializedCell.effectSlot] using unique) caller
  simp only [List.map_map] at related
  exact related

theorem effects_slots_unique : (Effects.slots.map Prod.fst).Nodup := by decide

theorem effects_slots_separate : ∀ slot ∈ Effects.slots, slot.1.startsWith "function$" = false := by
  intro slot member
  apply String.startsWith_string_eq_false_iff.mpr
  have absent : ∀ slot ∈ Effects.slots, ¬ ("function$".toList <+: slot.1.toList) := by decide
  exact absent slot member

theorem initialized_effects_unique {cells : List InitializedCell}
    (names : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots) :
    (cells.map InitializedCell.name).Nodup := by
  have equality := congrArg (List.map Prod.fst) names
  simp only [List.map_map] at equality
  change cells.map InitializedCell.name = Effects.slots.map Prod.fst at equality
  rw [equality]
  exact effects_slots_unique

theorem initialized_effects_separate {cells : List InitializedCell}
    (names : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots) :
    EffectSlotsSeparate (cells.map InitializedCell.effectSlot) := by
  intro slot member
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  have inSlots : (cell.name, cell.type) ∈ Effects.slots := by
    rw [← names]
    exact List.mem_map.mpr ⟨cell, cellMember, rfl⟩
  exact effects_slots_separate _ inSlots

end Solcore.Frontend.RustHull.Correspondence
