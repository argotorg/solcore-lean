import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix

/-! Nominal entries produced by the actual compatible catalog factory retain
the complete source constructor list. Finished native definitions have exactly
that many payloads; pending recursive reservations remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
open Core Frontend SourceInference SourceCoreCompatibleCatalog
open CompatibleCatalogRegistrationPrefix

def EntryShape (signatures : ProgramSignatures) (entry : Entry) : Prop :=
  ∀ declaration arguments, SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments) →
    ∃ signature, signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature] ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      ∀ definition, entry.definition = some definition →
        definition.constructorPayloadTypes.length = signature.constructors.length

def Shapes (signatures : ProgramSignatures) (catalog : Catalog) : Prop :=
  ∀ entry ∈ catalog.entries, EntryShape signatures entry

def Complete (catalog : Catalog) : Prop :=
  ∀ entry ∈ catalog.entries, entry.definition.isSome = true

theorem Shapes.empty (signatures : ProgramSignatures) (callableContracts : Bool) :
    Shapes signatures {callableContracts} := by
  intro entry member
  cases member

private theorem Shapes.append {signatures : ProgramSignatures} {catalog : Catalog} {entry : Entry}
    (previous : Shapes signatures catalog) (added : EntryShape signatures entry) :
    Shapes signatures {catalog with entries := catalog.entries ++ [entry]} := by
  intro item member
  rcases List.mem_append.mp member with member | member
  · exact previous item member
  · exact List.mem_singleton.mp member ▸ added

private theorem modify_preserves {α : Type} (property : α → Prop) (entries : List α)
    (index : Nat) (update : α → α) (previous : ∀ entry ∈ entries, property entry)
    (updated : ∀ entry, entries[index]? = some entry → property (update entry)) :
    ∀ entry ∈ entries.modify index update, property entry := by
  induction entries generalizing index with
  | nil => intro entry member; simp at member
  | cons head tail ih =>
    cases index with
    | zero =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact updated head rfl
      · exact previous entry (by simp [member])
    | succ index =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact previous entry (by simp)
      · exact ih index (fun item member => previous item (by simp [member]))
          (fun item found => updated item found) entry member

private theorem install_preserves {signatures : ProgramSignatures} {before after : Catalog}
    {entry : Entry} (payloads : List Ty)
    (extension : EntriesExtend {before with entries := before.entries ++ [entry]} after)
    (previous : Shapes signatures after)
    (updated : EntryShape signatures {entry with definition := some ⟨payloads⟩}) :
    Shapes signatures {after with entries := after.entries.modify before.entries.length (fun item => {item with definition := some ⟨payloads⟩})} := by
  apply modify_preserves _ _ _ _ previous
  intro item found
  have original : ({before with entries := before.entries ++ [entry]} : Catalog).entries[before.entries.length]? = some entry := by
    simp
  have same := extension.lookup original
  have equal := Option.some.inj (found.symm.trans same)
  subst item
  exact updated

private theorem nonnominal {signatures : ProgramSignatures} {entry : Entry}
    (absent : SourceCoreDataCatalog.nominalParts entry.sourceType = none) : EntryShape signatures entry := by
  intro declaration arguments found
  rw [absent] at found
  cases found

private theorem reservation {signatures : ProgramSignatures} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {signature : ProgramDataSignature}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature]) :
    EntryShape signatures ⟨type, none, signature.constructors.map (·.id)⟩ := by
  intro actual parameters found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nominal.symm.trans found))
  exact ⟨signature, selected, rfl, fun _ impossible => by cases impossible⟩

private theorem installed {signatures : ProgramSignatures} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {signature : ProgramDataSignature}
    {payloads : List Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (count : payloads.length = signature.constructors.length) :
    EntryShape signatures ⟨type, some ⟨payloads.map (Ty.product .word)⟩, signature.constructors.map (·.id)⟩ := by
  intro actual parameters found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nominal.symm.trans found))
  refine ⟨signature, selected, rfl, ?_⟩
  intro definition same
  cases same
  simpa using count

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem exact_signature {signatures : ProgramSignatures} {declaration : Resolved.DeclarationId}
    {signature : ProgramDataSignature}
    (accepted : (match signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
      | [] => throw (Error.catalog (.missingData declaration))
      | [signature] => pure signature
      | _ => throw (Error.catalog (.ambiguousData declaration))) = (Except.ok signature : Except SourceCoreCompatibleCatalog.Error ProgramDataSignature)) :
    signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature] := by
  split at accepted
  · cases accepted
  · cases accepted; assumption
  · cases accepted

theorem registered_shapes (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, Shapes signatures before →
      registerType signatures fuel before original = .ok (after, type) → Shapes signatures after) ∧
    (∀ before originals after types, Shapes signatures before →
      registerTypes signatures fuel before originals = .ok (after, types) →
        Shapes signatures after ∧ types.length = originals.length) := by
  induction fuel with
  | zero =>
    constructor
    · intro before original after type previous accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact previous
        · cases accepted
      · cases accepted
    · intro before originals after types previous accepted
      cases originals with
      | nil => cases accepted; exact ⟨previous, rfl⟩
      | cons => cases accepted
  | succ fuel ih =>
    constructor
    · intro before original after type previous accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact previous
        · split at accepted
          · obtain ⟨native, _, accepted⟩ := bind_ok accepted
            cases accepted
            exact previous
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact ih.1 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact ih.1 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
          · obtain ⟨registered, child, accepted⟩ := bind_ok accepted
            cases accepted
            rename_i inner view
            have absent : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = none := by rw [view]; rfl
            have reserved := previous.append (nonnominal (entry := ⟨SourceCoreRawMetadata.runtimeType original, none, []⟩) absent)
            exact install_preserves _ (registerType_entries child) (ih.1 _ _ _ _ reserved child)
              (nonnominal absent)
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            rename_i key value view
            have absent : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = none := by rw [view]; rfl
            have reserved := previous.append (nonnominal (entry := ⟨SourceCoreRawMetadata.runtimeType original, none, []⟩) absent)
            have shaped := ih.1 _ _ _ _ (ih.1 _ _ _ _ reserved initial) final
            exact install_preserves _ ((registerType_entries initial).trans (registerType_entries final)) shaped
              (nonnominal absent)
          · split at accepted
            · obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
              have selected := exact_signature selected
              split at accepted
              · split at accepted
                · obtain ⟨_, _, accepted⟩ := bind_ok accepted
                  obtain ⟨registered, child, accepted⟩ := bind_ok accepted
                  cases accepted
                  have reserved := previous.append (reservation (by assumption) selected)
                  obtain ⟨shaped, count⟩ := ih.2 _ _ _ _ reserved child
                  apply install_preserves _ (registerTypes_entries child) shaped
                  apply installed (by assumption) selected
                  simpa using count
                · cases accepted
              · cases accepted
            · cases accepted
      · cases accepted
    · intro before originals after types previous accepted
      cases originals with
      | nil => cases accepted; exact ⟨previous, rfl⟩
      | cons original rest =>
        obtain ⟨first, initial, remaining⟩ := bind_ok accepted
        obtain ⟨tail, final, accepted⟩ := bind_ok remaining
        cases accepted
        obtain ⟨shaped, count⟩ := ih.2 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
        exact ⟨shaped, by simpa using count⟩

theorem registerType_shapes {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (previous : Shapes signatures before)
    (accepted : registerType signatures fuel before original = .ok (after, type)) : Shapes signatures after :=
  (registered_shapes signatures fuel).1 _ _ _ _ previous accepted

theorem registerTypes_shapes {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (previous : Shapes signatures before)
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    Shapes signatures after ∧ types.length = originals.length :=
  (registered_shapes signatures fuel).2 _ _ _ _ previous accepted

theorem prepare_shapes {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked) :
    Shapes signatures checked.catalog := by
  unfold prepare at accepted
  obtain ⟨registered, produced, accepted⟩ := bind_ok accepted
  rcases registered with ⟨catalog, nativeTypes⟩
  have shaped := (registerTypes_shapes (Shapes.empty signatures callableContracts) produced).1
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  rcases discovered with ⟨seen, original⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact shaped
    · cases accepted

theorem identity_entry {catalog : Catalog} {original : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? original = some identity) :
    ∃ entry, catalog.entries[identity.index]? = some entry ∧
      entry.sourceType = SourceCoreRawMetadata.runtimeType original := by
  unfold Catalog.identity? at found
  cases selected : catalog.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType original)) with
  | none => simp [selected] at found
  | some item =>
    rcases item with ⟨entry, index⟩
    simp only [selected, Option.map_some, Option.some.injEq] at found
    subst identity
    have member := List.mem_of_find?_eq_some selected
    have sourceEq : entry.sourceType = SourceCoreRawMetadata.runtimeType original := by
      simpa using List.find?_some selected
    exact ⟨entry, List.mk_mem_zipIdx_iff_getElem?.mp member, sourceEq⟩

private theorem finished_of_forIn {entries : List (Entry × Nat)} {output : Unit}
    (accepted : forIn entries () (fun item _ => do
      if item.1.definition.isNone then throw (Error.catalog (.unfinishedDefinition item.2))
      pure (.yield ())) = (Except.ok output : Except SourceCoreCompatibleCatalog.Error Unit)) :
    ∀ item ∈ entries, item.1.definition.isSome = true := by
  induction entries with
  | nil => intro item member; cases member
  | cons item rest ih =>
    cases stored : item.1.definition with
    | none => simp [List.forIn_cons, stored, throw, bind, Except.bind] at accepted
    | some definition =>
      have remaining : forIn rest () (fun item _ => do
          if item.1.definition.isNone then throw (Error.catalog (.unfinishedDefinition item.2))
          pure (.yield ())) = (Except.ok output : Except SourceCoreCompatibleCatalog.Error Unit) := by
        simpa [List.forIn_cons, stored, pure, Except.pure, bind, Except.bind] using accepted
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · simp [stored]
      · exact ih remaining actual member

theorem prepare_complete {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked) :
    Complete checked.catalog := by
  unfold prepare at accepted
  obtain ⟨registered, _, accepted⟩ := bind_ok accepted
  rcases registered with ⟨catalog, nativeTypes⟩
  obtain ⟨output, finished, accepted⟩ := bind_ok accepted
  have complete : Complete catalog := by
    intro entry member
    obtain ⟨index, found⟩ := List.getElem?_of_mem member
    have zipped : (entry, index) ∈ catalog.entries.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr found
    exact finished_of_forIn finished (entry, index) zipped
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  rcases discovered with ⟨seen, original⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact complete
    · cases accepted

theorem Shapes.nominal_coverage {signatures : ProgramSignatures} {catalog : Catalog}
    (shaped : Shapes signatures catalog)
    (complete : Complete catalog)
    {original : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {signature : ProgramDataSignature} {identity : DataTypeId} {definition : DataDefinition}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (found : catalog.identity? original = some identity)
    (registered : catalog.definitions.lookupDataType? identity = some definition) :
    ∃ entry, catalog.entries[identity.index]? = some entry ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      definition.constructorPayloadTypes.length = signature.constructors.length := by
  obtain ⟨entry, entryAt, sourceEq⟩ := identity_entry found
  obtain ⟨actual, exact, ids, count⟩ := shaped entry (List.mem_of_getElem? entryAt)
    declaration arguments (by rw [sourceEq]; exact nominal)
  have same := List.singleton_inj.mp (exact.symm.trans selected)
  subst actual
  have definitionAt : entry.definition = some definition := by
    simp only [DataEnvironment.lookupDataType?, Catalog.definitions, List.getElem?_map, entryAt,
      Option.map_some, Option.some.injEq] at registered
    cases stored : entry.definition with
    | none =>
      have present := complete entry (List.mem_of_getElem? entryAt)
      simp [stored] at present
    | some stored => simpa [stored] using congrArg some registered
  exact ⟨entry, entryAt, ids, count definition definitionAt⟩

theorem prepare_nominal_coverage {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked)
    {original : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {signature : ProgramDataSignature} {identity : DataTypeId} {definition : DataDefinition}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (declaration, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (found : checked.catalog.identity? original = some identity)
    (registered : checked.catalog.definitions.lookupDataType? identity = some definition) :
    ∃ entry, checked.catalog.entries[identity.index]? = some entry ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      definition.constructorPayloadTypes.length = signature.constructors.length := by
  have owner := prepare_signatures accepted
  rw [owner] at selected
  exact (prepare_shapes accepted).nominal_coverage (prepare_complete accepted) nominal selected found registered

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
