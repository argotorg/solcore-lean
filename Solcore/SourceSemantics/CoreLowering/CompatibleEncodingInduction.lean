import Solcore.SourceSemantics.CoreLowering.CompatibleEncodingFacts

/-! Induction interfaces and list/default steps for the actual compatible
encoder. These steps will be closed by induction on its fuel; they never
substitute a second encoder for the executable implementation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
open Core Frontend Frontend.SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreCompatibleValues (encodeRaw encodePayloadsRaw encodeEntriesRaw encodeDefaultRaw)

variable (checked : Checked) (functions : FunctionModel checked.catalog) (mapping : LocationMap) (world : StoreTyping)

def RawSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ expected carrier (encoded : Extended registry Value) type,
    encodeRaw fuel checked registry expected carrier = .ok encoded →
    checked.catalog.project expected = .ok type →
    RuntimeValueHasType world encoded.value type checked.catalog.definitions →
    ∃ source, Means carrier source ∧ ValueRep checked encoded.registry functions mapping world expected source encoded.value type

def PayloadSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ types carriers index (encoded : Extended registry Value) coreTypes,
    encodePayloadsRaw fuel checked registry types carriers index = .ok encoded →
    types.mapM checked.catalog.project = .ok coreTypes →
    RuntimeValueHasType world encoded.value (SourceCoreCompatibleCatalog.packTypes coreTypes) checked.catalog.definitions →
    ∃ sources values, Meanings carriers sources ∧ ValuesRep checked encoded.registry functions mapping world types sources values coreTypes ∧
      encoded.value = packValues values

def EntriesSound (fuel : Nat) : Prop := ∀ (registry : Registry), registry.signatures = checked.signatures →
  ∀ keyType valueType layout carriers index (encoded : Extended registry Value),
    encodeEntriesRaw fuel checked registry keyType valueType layout carriers index = .ok encoded →
    checked.catalog.project keyType = .ok layout.keyType → checked.catalog.project valueType = .ok layout.valueType →
    layout.Registered checked.catalog.definitions →
    RuntimeValueHasType world encoded.value layout.type checked.catalog.definitions →
    ∃ sources entries, EntryMeanings carriers sources ∧
      EntriesRep checked encoded.registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType ∧
      encoded.value = OrderedMapping.encode layout entries

variable {checked functions mapping world}

theorem default_sound {fuel : Nat} (induction : RawSound checked functions mapping world fuel)
    {registry : Registry} (owner : registry.signatures = checked.signatures)
    {sourceType : TypeSystem.Ty} {type : Ty} {encoded : Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded)
    (projected : checked.catalog.project sourceType = .ok type) (wf : type.WellFormed checked.catalog.definitions)
    (typed : RuntimeValueHasType world encoded.value (.sum .unit type) checked.catalog.definitions) :
    ∃ fallback, encoded.value = OrderedMapping.optionValue type fallback ∧
      DefaultRep checked encoded.registry functions mapping world sourceType fallback type := by
  cases found : SourceCoreCompatibleValues.defaultValue? (sourceType.size + 1) sourceType with
  | none =>
    simp only [encodeDefaultRaw, found, pure, Except.pure] at accepted
    cases accepted
    exact ⟨none, rfl, .absent ((CompatiblePayload.defaultValue?_absent_iff (by omega)).mp
      ((SourceCoreCompatibleValues.defaultValue?_absent_iff _ _).mp found)) projected wf⟩
  | some carrier =>
    simp only [encodeDefaultRaw, found] at accepted
    obtain ⟨inner, generated, accepted⟩ := bind_ok accepted
    cases accepted
    cases typed with
    | inRight typed =>
      obtain ⟨source, means, related⟩ := induction registry owner sourceType carrier inner type generated projected typed
      obtain ⟨actual, meaning, actualMeans⟩ := default_meaning found
      have same := means.functional actualMeans
      subst actual
      exact ⟨some inner.value, rfl, .present meaning related⟩

/-- Child payload representations can be transported across later registry
allocations without changing their source values or native bytes. -/
theorem values_extend {registry future : Registry} {types : List TypeSystem.Ty} {sources : List Dynamic.Value}
    {values : List Value} {coreTypes : List Ty}
    (related : ValuesRep checked registry functions mapping world types sources values coreTypes)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    ValuesRep checked future functions mapping world types sources values coreTypes := by
  induction types generalizing sources values coreTypes with
  | nil => cases related; exact .nil
  | cons type types ih => cases related with
    | cons head tail => exact .cons (head.extend extension ⟨[], by simp⟩ ⟨[], by simp⟩) (ih tail)

theorem payload_zero : PayloadSound checked functions mapping world 0 := by
  intro registry owner types carriers index encoded coreTypes accepted projected typed
  cases types with
  | nil => cases carriers with
    | nil =>
      simp [encodePayloadsRaw] at accepted
      subst encoded
      cases projected
      exact ⟨[], [], .nil, .nil, rfl⟩
    | cons => simp [encodePayloadsRaw, bind, Except.bind, throw, throwThe] at accepted
  | cons head tail =>
    simp only [encodePayloadsRaw] at accepted
    split at accepted <;> simp_all [pure, Except.pure, bind, Except.bind, throw, throwThe]

theorem entries_zero : EntriesSound checked functions mapping world 0 := by
  intro registry owner keyType valueType layout carriers index encoded accepted first second registered typed
  cases carriers with
  | nil => simp only [encodeEntriesRaw, pure, Except.pure] at accepted; cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
  | cons => simp [encodeEntriesRaw, throw, throwThe] at accepted

/-- The actual ordered-list encoder consumes keys and values in their stored
order, then extends earlier metadata receipts across the remaining entries. -/
theorem entries_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (tail : EntriesSound checked functions mapping world fuel) :
    EntriesSound checked functions mapping world (fuel + 1) := by
  intro registry owner keyType valueType layout carriers index encoded accepted first second registered typed
  cases carriers with
  | nil => simp only [encodeEntriesRaw, pure, Except.pure] at accepted; cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
  | cons entry rest =>
    rcases entry with ⟨key, value⟩
    simp only [encodeEntriesRaw] at accepted
    obtain ⟨keyEncoded, keyAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨valueEncoded, valueAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨restEncoded, restAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    cases typed with
    | constructed lookup payloadTyped =>
      have same := Option.some.inj (lookup.symm.trans registered.consLookup)
      subst_vars
      cases payloadTyped with
      | pair entryTyped restTyped => cases entryTyped with
        | pair keyTyped valueTyped =>
          obtain ⟨sourceKey, keyMeans, keyRep⟩ := raw registry owner _ _ _ _ (mapError_ok keyAccepted) first keyTyped
          obtain ⟨sourceValue, valueMeans, valueRep⟩ := raw keyEncoded.registry (keyEncoded.preserves.signatures.trans owner)
            _ _ _ _ (mapError_ok valueAccepted) second valueTyped
          obtain ⟨sources, entries, restMeans, restRep, encoding⟩ := tail valueEncoded.registry
            (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
            _ _ _ _ _ _ restAccepted first second registered restTyped
          exact ⟨(sourceKey, sourceValue) :: sources, (keyEncoded.value, valueEncoded.value) :: entries,
            .prepend keyMeans valueMeans restMeans,
            .entry (keyRep.extend (valueEncoded.preserves.trans restEncoded.preserves) ⟨[], by simp⟩ ⟨[], by simp⟩)
              (valueRep.extend restEncoded.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) restRep,
            by simp [OrderedMapping.encode, encoding]⟩

theorem project_cons {head : TypeSystem.Ty} {tail : List TypeSystem.Ty} {types : List Ty}
    (projected : (head :: tail).mapM checked.catalog.project = .ok types) :
    ∃ type rest, checked.catalog.project head = .ok type ∧ tail.mapM checked.catalog.project = .ok rest ∧ types = type :: rest := by
  cases first : checked.catalog.project head with
  | error => simp [List.mapM_cons, first, bind, Except.bind] at projected
  | ok type =>
    cases remaining : tail.mapM checked.catalog.project with
    | error => simp [List.mapM_cons, first, remaining, bind, Except.bind] at projected
    | ok rest =>
      simp [List.mapM_cons, first, remaining, bind, Except.bind] at projected
      subst types
      exact ⟨type, rest, rfl, rfl, rfl⟩

theorem payload_succ {fuel : Nat} (raw : RawSound checked functions mapping world fuel)
    (tail : PayloadSound checked functions mapping world fuel) :
    PayloadSound checked functions mapping world (fuel + 1) := by
  intro registry owner types carriers index encoded coreTypes accepted projected typed
  by_cases length : types.length = carriers.length
  · cases types with
    | nil => cases carriers with
      | nil =>
        simp [encodePayloadsRaw] at accepted
        subst encoded
        cases projected
        exact ⟨[], [], .nil, .nil, rfl⟩
      | cons => simp at length
    | cons type types => cases carriers with
      | nil => simp at length
      | cons carrier carriers =>
        obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ := project_cons projected
        cases types with
        | nil =>
          have empty : carriers = [] := by simpa using length.symm
          subst carriers
          cases remainingProjection
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨source, means, represented⟩ := raw registry owner _ _ _ _ (mapError_ok accepted) firstProjection typed
          exact ⟨[source], [encoded.value], .cons means .nil, .cons represented .nil, rfl⟩
        | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ := project_cons remainingProjection
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨first, firstAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨rest, restAccepted, accepted⟩ := bind_ok accepted
          cases accepted
          cases typed with
          | pair firstTyped restTyped =>
            obtain ⟨source, means, represented⟩ := raw registry owner _ _ _ _ (mapError_ok firstAccepted) firstProjection firstTyped
            obtain ⟨sources, values, meanings, representations, packing⟩ := tail first.registry
              (first.preserves.signatures.trans owner) _ _ _ _ _ restAccepted remainingProjection restTyped
            cases values with
            | nil => cases representations
            | cons head values =>
              exact ⟨source :: sources, first.value :: head :: values, .cons means meanings,
                .cons (represented.extend rest.preserves ⟨[], by simp⟩ ⟨[], by simp⟩) representations,
                by simp only [packValues]; rw [packing]⟩
  · unfold encodePayloadsRaw at accepted
    simp [length, bind, Except.bind, throw, throwThe] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
