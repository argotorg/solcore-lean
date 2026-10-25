import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! Reserved runtime references retain their actual locations under source
binders and compiler-generated administrative prefixes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

structure EffectSlot where
  name : String
  type : Core.Ty
  location : Nat

def EffectEnvironmentRel (slots : List EffectSlot) (scope : Scope)
    (mapping : Core.Renaming) (environment : Core.Environment) : Prop :=
  ∀ slot ∈ slots, ∀ binding index,
    scope.lookup (Effects.slotName slot.name) = .ok (binding, index) →
    environment[mapping index]? = some (.cellRef slot.type slot.location)

theorem EffectEnvironmentRel.empty (scope : Scope) (mapping : Core.Renaming)
    (environment : Core.Environment) : EffectEnvironmentRel [] scope mapping environment := by
  intro slot member
  cases member

theorem EffectEnvironmentRel.temporary {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment)
    (type : Core.Ty) (value : Core.Value) :
    EffectEnvironmentRel slots (scope.temporary type) mapping.lift (value :: environment) := by
  intro slot member binding index looked
  rw [Scope.temporary, scope_lookup_cons] at looked
  simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem EffectEnvironmentRel.addLocal {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (allowed : name.startsWith Effects.reservedPrefix = false) :
    EffectEnvironmentRel slots (scope.addLocal name type) mapping.lift (value :: environment) := by
  intro slot member binding index looked
  have different : name ≠ Effects.slotName slot.name := by
    intro same
    have reserved := slotName_reserved slot.name
    rw [← same, allowed] at reserved
    contradiction
  rw [Scope.addLocal, scope_lookup_cons] at looked
  simp only [Option.some_beq_some, beq_iff_eq, different, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem EffectEnvironmentRel.prepend {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment) (extra : Core.Environment) :
    EffectEnvironmentRel slots scope (fun index => extra.length + mapping index) (extra ++ environment) := by
  intro slot member binding index looked
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    using related slot member binding index looked

end Solcore.Frontend.RustHull.Correspondence
