import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.Core.DefinitionExtension
/-! Successful compatible type registration preserves every existing entry.
The exact fuel induction follows the production reserve/register/install calls,
including recursive nominal payloads. This yields native definition extensions;
complete constructor coverage still requires a separate factory invariant. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix
open Core Frontend SourceInference SourceCoreCompatibleCatalog

def EntriesExtend (before after : Catalog) : Prop :=
  ∃ suffix, after.entries = before.entries ++ suffix

theorem EntriesExtend.refl (catalog : Catalog) : EntriesExtend catalog catalog := ⟨[], by simp⟩

theorem EntriesExtend.trans {before middle after : Catalog}
    (first : EntriesExtend before middle) (last : EntriesExtend middle after) : EntriesExtend before after := by
  obtain ⟨left, first⟩ := first
  obtain ⟨right, last⟩ := last
  exact ⟨left ++ right, by rw [last, first, List.append_assoc]⟩

private theorem modify_suffix {α : Type} (front rest : List α) (index : Nat) (update : α → α) :
    (front ++ rest).modify (front.length + index) update = front ++ rest.modify index update := by
  induction front with
  | nil => simp
  | cons head tail ih => simpa [List.modify, Nat.succ_add] using congrArg (List.cons head) ih

private theorem install_suffix {before middle : Catalog} {entry : Entry} (update : Entry → Entry)
    (extension : EntriesExtend {before with entries := before.entries ++ [entry]} middle) :
    ∃ suffix, middle.entries.modify before.entries.length update = before.entries ++ suffix := by
  obtain ⟨suffix, extended⟩ := extension
  refine ⟨([entry] ++ suffix).modify 0 update, ?_⟩
  rw [extended, List.append_assoc]
  exact modify_suffix before.entries ([entry] ++ suffix) 0 update

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Only registered Source types are used to justify concrete preparation. -/
def ClosedSources (catalog : Catalog) : Prop :=
  ∀ entry, entry ∈ catalog.entries → SourceCoreDataCatalog.closed entry.sourceType = true

/-- The same registration fold retains its source closure invariant beside
its original append-only entry prefix. -/
structure Registered (before after : Catalog) : Prop where
  entries : EntriesExtend before after
  closed : ClosedSources before → ClosedSources after

theorem Registered.refl (catalog : Catalog) : Registered catalog catalog :=
  ⟨EntriesExtend.refl catalog, fun closed => closed⟩

theorem Registered.trans {before middle after : Catalog}
    (first : Registered before middle) (last : Registered middle after) : Registered before after :=
  ⟨first.entries.trans last.entries, fun closed => last.closed (first.closed closed)⟩

private theorem closed_modify (entries : List Entry) (index : Nat) (update : Entry → Entry)
    (same : ∀ entry, (update entry).sourceType = entry.sourceType)
    (closed : ∀ entry, entry ∈ entries → SourceCoreDataCatalog.closed entry.sourceType = true) :
    ∀ entry, entry ∈ entries.modify index update → SourceCoreDataCatalog.closed entry.sourceType = true := by
  induction entries generalizing index with
  | nil => intro entry member; simp only [List.modify_nil, List.not_mem_nil] at member
  | cons head tail ih =>
    cases index with
    | zero =>
      intro entry member
      simp only [List.modify_zero_cons, List.mem_cons] at member
      rcases member with rfl | member
      · rw [same]; exact closed head List.mem_cons_self
      · exact closed entry (List.mem_cons_of_mem _ member)
    | succ index =>
      intro entry member
      simp only [List.modify_succ_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact closed _ List.mem_cons_self
      · exact ih index (fun entry member => closed entry (List.mem_cons_of_mem _ member)) entry member

private theorem installed {before middle : Catalog} {entry : Entry} (update : Entry → Entry)
    (same : ∀ item, (update item).sourceType = item.sourceType)
    (entryClosed : SourceCoreDataCatalog.closed entry.sourceType = true)
    (extension : Registered {before with entries := before.entries ++ [entry]} middle) :
    Registered before {middle with entries := middle.entries.modify before.entries.length update} := by
  refine ⟨install_suffix update extension.entries, ?_⟩
  intro beforeClosed
  apply closed_modify _ _ _ same
  apply extension.closed
  intro item member
  rcases List.mem_append.mp member with old | fresh
  · exact beforeClosed item old
  · exact List.mem_singleton.mp fresh ▸ entryClosed

theorem registered_prefix_with_closed (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, registerType signatures fuel before original = .ok (after, type) → Registered before after) ∧
    (∀ before originals after types, registerTypes signatures fuel before originals = .ok (after, types) → Registered before after) := by
  induction fuel with
  | zero =>
    constructor
    · intro before original after type accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · rename_i closed
        split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact .refl _
        · cases accepted
      · cases accepted
    · intro before originals after types accepted
      cases originals with
      | nil => cases accepted; exact .refl _
      | cons => cases accepted
  | succ fuel ih =>
    constructor
    · intro before original after type accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · rename_i closed
        split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact .refl _
        · split at accepted
          · obtain ⟨native, _, accepted⟩ := bind_ok accepted
            cases accepted
            exact .refl _
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
          · obtain ⟨registered, child, accepted⟩ := bind_ok accepted
            cases accepted
            have extension := ih.1 _ _ _ _ child
            exact installed _ (fun _ => rfl) closed extension
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            have extension := (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
            exact installed _ (fun _ => rfl) closed extension
          · split at accepted
            · obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
              split at accepted
              · split at accepted
                · obtain ⟨_, _, accepted⟩ := bind_ok accepted
                  obtain ⟨registered, child, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact installed _ (fun _ => rfl) closed (ih.2 _ _ _ _ child)
                · cases accepted
              · cases accepted
            · cases accepted
      · cases accepted
    · intro before originals after types accepted
      cases originals with
      | nil => cases accepted; exact .refl _
      | cons original rest =>
        obtain ⟨first, initial, remaining⟩ := bind_ok accepted
        obtain ⟨tail, final, accepted⟩ := bind_ok remaining
        cases accepted
        exact (ih.1 _ _ _ _ initial).trans (ih.2 _ _ _ _ final)

/-- The original registration interface forgets only the closed-source invariant. -/
theorem registered_prefix (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, registerType signatures fuel before original = .ok (after, type) → EntriesExtend before after) ∧
    (∀ before originals after types, registerTypes signatures fuel before originals = .ok (after, types) → EntriesExtend before after) := by
  exact ⟨fun _ _ _ _ accepted => ((registered_prefix_with_closed signatures fuel).1 _ _ _ _ accepted).entries,
    fun _ _ _ _ accepted => ((registered_prefix_with_closed signatures fuel).2 _ _ _ _ accepted).entries⟩

theorem EntriesExtend.definitions {before after : Catalog} (extension : EntriesExtend before after) :
    before.definitions.Extends after.definitions := by
  obtain ⟨suffix, extended⟩ := extension
  refine ⟨suffix.map (fun entry => entry.definition.getD ⟨[]⟩), ?_⟩
  simp only [Catalog.definitions, extended, List.map_append]

theorem EntriesExtend.lookup {before after : Catalog} (extension : EntriesExtend before after)
    {index : Nat} {entry : Entry} (found : before.entries[index]? = some entry) :
    after.entries[index]? = some entry := by
  obtain ⟨suffix, extended⟩ := extension
  rw [extended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem EntriesExtend.identity {before after : Catalog} (extension : EntriesExtend before after)
    {original : TypeSystem.Ty} {identity : DataTypeId}
    (found : before.identity? original = some identity) : after.identity? original = some identity := by
  obtain ⟨suffix, extended⟩ := extension
  unfold Catalog.identity? at found ⊢
  rw [extended, List.zipIdx_append, List.find?_append]
  cases selected : before.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType original)) with
  | none => simp [selected] at found
  | some entry => simpa [selected, Option.or] using found

theorem registerType_entries {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (accepted : registerType signatures fuel before original = .ok (after, type)) :
    EntriesExtend before after := (registered_prefix signatures fuel).1 _ _ _ _ accepted

theorem registerTypes_entries {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    EntriesExtend before after := (registered_prefix signatures fuel).2 _ _ _ _ accepted

theorem registerType_definitions {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (accepted : registerType signatures fuel before original = .ok (after, type)) :
    before.definitions.Extends after.definitions := (registerType_entries accepted).definitions

theorem registerTypes_definitions {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    before.definitions.Extends after.definitions := (registerTypes_entries accepted).definitions

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix
