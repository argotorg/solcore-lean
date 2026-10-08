import Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
import Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates

/-! Static provenance of the actual expanded missing-diagnostic rows.
Each returned row retains its real public site and raw owning metadata.
Duplicate tokens keep the original producer's first row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

/-- A row actually emitted for a matching raw mapping header. -/
def MissingRow (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (row : Word × Diagnostic) : Prop :=
  ∃ site, site ∈ sites ∧ ∃ index rawKey rawValue,
    (SourceCoreRawMetadata.Metadata.mapping rawKey rawValue, index) ∈ registry.entries.zipIdx ∧
    SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
    SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType ∧
    Word.ofNat? (site.base.val + index + 1) = some row.1 ∧
    row.2 = { error := .typeMismatch rawValue none, site := site.site, span := some site.span }

private def RowsSound (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (rows : List (Word × Diagnostic)) : Prop := ∀ row, row ∈ rows → MissingRow registry sites row

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_contains {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {property : β → Prop} {selected : α}
    (accepted : forIn items initial step = .ok final) (member : selected ∈ items)
    (each : ∀ item, item ∈ items → ∀ state outcome, step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ (property state → property updated) ∧
        (item = selected → property updated)) : property final := by
  have contains : selected ∈ items → property final := by
    apply CompatibleMemberCertificates.forIn_preserves accepted
      (fun seen state => selected ∈ seen → property state)
    · simp
    · intro seen item remaining state outcome split previous ran
      have member : item ∈ items := by rw [split]; simp
      obtain ⟨updated, rfl, keeps, obtains⟩ := each item member state outcome ran
      refine ⟨updated, rfl, ?_⟩
      intro appeared
      rcases List.mem_append.mp appeared with before | current
      · exact keeps (previous before)
      · have same := List.mem_singleton.mp current
        exact obtains same.symm
  exact contains member

private theorem contains_append {reason : Word} {rows suffix : List (Word × Diagnostic)}
    (present : ∃ row, row ∈ rows ∧ row.1 = reason) :
    ∃ row, row ∈ rows ++ suffix ∧ row.1 = reason := by
  obtain ⟨row, member, same⟩ := present
  exact ⟨row, List.mem_append_left _ member, same⟩

/-- Soundness follows the actual two finite inventory loops. -/
theorem missingDiagnostics_rows {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows) :
    ∀ row, row ∈ rows → MissingRow registry sites row := by
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    have same := Except.ok.inj finished
    subst updated
    apply CompatibleMemberCertificates.forIn_preserves loop (fun _ output => RowsSound registry sites output)
    · intro row member
      cases member
    · intro seen site remaining state outcome split previous ran
      have member : site ∈ sites := by rw [split]; simp
      obtain ⟨updated, inner, finished⟩ := bind_ok ran
      refine ⟨updated, (Except.ok.inj finished).symm, ?_⟩
      apply CompatibleMemberCertificates.forIn_preserves inner (fun _ output => RowsSound registry sites output) previous
      intro seen entry remaining state outcome split previous ran
      obtain ⟨metadata, index⟩ := entry
      dsimp only at ran
      have stored : (metadata, index) ∈ registry.entries.zipIdx := by rw [split]; simp
      cases metadata with
      | proxy inner =>
        exact ⟨state, (Except.ok.inj ran).symm, previous⟩
      | constructor instantiation =>
        exact ⟨state, (Except.ok.inj ran).symm, previous⟩
      | mapping rawKey rawValue =>
        dsimp only at ran
        split at ran
        · rename_i matched
          have views : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
              SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using matched
          obtain ⟨reason, generated, finished⟩ := bind_ok ran
          have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
            change (match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason at generated
            split at generated
            · cases generated; assumption
            · cases generated
          split at finished
          · exact ⟨state, (Except.ok.inj finished).symm, previous⟩
          · refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
            intro row rowMember
            rcases List.mem_append.mp rowMember with old | fresh
            · exact previous row old
            · have same := List.mem_singleton.mp fresh
              subst row
              exact ⟨site, member, index, rawKey, rawValue, stored, views.1, views.2, converted, rfl⟩
        · exact ⟨state, (Except.ok.inj ran).symm, previous⟩
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- A genuine matching public site and authenticated header are covered by
an actual returned token. A duplicate token retains its earlier diagnostic. -/
theorem missingDiagnostics_contains {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows)
    {site : MissingSite} (member : site ∈ sites) {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (reserved : site.base.val + header.val < wordModulus) :
    ∃ row, row ∈ rows ∧ row.1 = site.base.add header := by
  have positive : header.val ≠ 0 := by
    intro zero
    apply metadata.nonzero
    exact Fin.ext zero
  have stored : (.mapping rawKey rawValue, header.val - 1) ∈ registry.entries.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa [SourceCoreRawMetadata.Registry.lookup, positive] using metadata.lookup
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    have same := Except.ok.inj finished
    subst updated
    apply forIn_contains loop member
    intro current currentMember state outcome ran
    obtain ⟨updated, inner, finished⟩ := bind_ok ran
    refine ⟨updated, (Except.ok.inj finished).symm, ?_, ?_⟩
    · intro present
      apply CompatibleMemberCertificates.forIn_preserves inner (fun _ output =>
        ∃ row, row ∈ output ∧ row.1 = site.base.add header) present
      intro seen entry remaining state outcome split present ran
      obtain ⟨rawMetadata, index⟩ := entry
      dsimp only at ran
      cases rawMetadata with
      | proxy _ | constructor _ => exact ⟨state, (Except.ok.inj ran).symm, present⟩
      | mapping _ _ =>
        dsimp only at ran
        split at ran
        · obtain ⟨reason, _, finished⟩ := bind_ok ran
          split at finished
          · exact ⟨state, (Except.ok.inj finished).symm, present⟩
          · exact ⟨_, (Except.ok.inj finished).symm, contains_append present⟩
        · exact ⟨state, (Except.ok.inj ran).symm, present⟩
    · intro same
      subst current
      apply forIn_contains inner stored
      intro entry entryMember state outcome ran
      obtain ⟨rawMetadata, index⟩ := entry
      dsimp only at ran
      cases rawMetadata with
      | proxy _ | constructor _ =>
        refine ⟨state, (Except.ok.inj ran).symm, fun present => present, ?_⟩
        intro same
        cases same
      | mapping key value =>
        dsimp only at ran
        split at ran
        · obtain ⟨reason, generated, finished⟩ := bind_ok ran
          have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
            change (match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value
              | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason at generated
            split at generated
            · cases generated; assumption
            · cases generated
          have tokenEq (same : (SourceCoreRawMetadata.Metadata.mapping key value, index) =
              (.mapping rawKey rawValue, header.val - 1)) : reason = site.base.add header := by
            have indexEq := congrArg Prod.snd same
            have number : reason.val = site.base.val + index + 1 := by
              unfold Word.ofNat? at converted
              split at converted
              · exact congrArg Fin.val (Option.some.inj converted).symm
              · cases converted
            apply Fin.ext
            rw [token_nonWrapping site.base header header.val reserved (Nat.le_refl _)]
            omega
          split at finished
          · rename_i already
            refine ⟨state, (Except.ok.inj finished).symm, fun present => present, ?_⟩
            intro same
            obtain ⟨row, rowMember, equal⟩ := List.any_eq_true.mp already
            exact ⟨row, rowMember, (of_decide_eq_true equal).trans (tokenEq same)⟩
          · refine ⟨_, (Except.ok.inj finished).symm, contains_append, ?_⟩
            intro same
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), tokenEq same⟩
        · rename_i unmatched
          refine ⟨state, (Except.ok.inj ran).symm, fun present => present, ?_⟩
          intro same
          have types := congrArg Prod.fst same
          cases types
          have contradiction : (decide (SourceCoreRawMetadata.runtimeType rawKey =
              SourceCoreRawMetadata.runtimeType site.keyType) &&
              decide (SourceCoreRawMetadata.runtimeType rawValue =
                SourceCoreRawMetadata.runtimeType site.valueType)) = true := by simp [keyView, valueView]
          exact False.elim (unmatched contradiction)
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error
      (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- The producer's budget check applies to its actual output registry. -/
theorem missingDiagnostics_budget {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows) :
    registry.length ≤ registry.limits.maxEntries := by
  unfold missingDiagnostics at accepted
  split at accepted
  · assumption
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- Recover the actual one-based raw header and the same nonwrapping token. -/
theorem MissingRow.metadata {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {row : Word × Diagnostic} (rowOrigin : MissingRow registry sites row) :
    ∃ site, site ∈ sites ∧ ∃ rawKey rawValue header,
      MetadataRep registry (.mapping rawKey rawValue) header ∧
      SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
      SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType ∧
      row.1 = site.base.add header ∧ site.base.val + header.val < wordModulus ∧
      row.2 = { error := .typeMismatch rawValue none, site := site.site, span := some site.span } := by
  obtain ⟨site, member, index, rawKey, rawValue, stored, keyView, valueView, converted, diagnostic⟩ := rowOrigin
  have number : row.1.val = site.base.val + index + 1 := by
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  have bounded : index + 1 < wordModulus := by have := row.1.isLt; omega
  let header : Word := ⟨index + 1, bounded⟩
  have lookup : registry.lookup header = some (.mapping rawKey rawValue) := by
    have stored := List.mk_mem_zipIdx_iff_getElem?.mp stored
    simpa [SourceCoreRawMetadata.Registry.lookup, header] using stored
  have reserved : site.base.val + header.val < wordModulus := by
    have := row.1.isLt
    dsimp [header]
    omega
  refine ⟨site, member, rawKey, rawValue, header, ⟨lookup⟩, keyView, valueView, ?_, reserved, diagnostic⟩
  apply Fin.ext
  rw [token_nonWrapping site.base header header.val reserved (Nat.le_refl _)]
  simpa [header, Nat.add_assoc] using number

/-- Authentication gives a real one-based registry position. -/
theorem metadata_headerBound {registry : SourceCoreRawMetadata.Registry}
    {metadata : SourceCoreRawMetadata.Metadata} {header : Word}
    (represented : MetadataRep registry metadata header) : header.val ≤ registry.length := by
  have lookup := represented.lookup
  unfold SourceCoreRawMetadata.Registry.lookup at lookup
  split at lookup
  · cases lookup
  · rename_i positive
    have bounded := (List.getElem?_eq_some_iff.mp lookup).1
    change header.val ≤ registry.entries.length
    omega

/-- A successful extension table checks its actual registry's budget. -/
theorem tableForRegistry_budget {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table) :
    registry.length ≤ registry.limits.maxEntries := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, _⟩ := bind_ok accepted
  exact missingDiagnostics_budget built

/-- Real site membership, an authenticated extended-registry header and its
reserved range give a row in the actual rebuilt public table. -/
theorem tableForRegistry_contains {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (reserved : site.base.val + registry.limits.maxEntries < wordModulus) :
    ∃ row, row ∈ table.additional ∧ row.1 = site.base.add header ∧
      MissingRow registry program.missing row := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst table
  have budget := missingDiagnostics_budget built
  have bounded := metadata_headerBound metadata
  have within : site.base.val + header.val < wordModulus := by omega
  obtain ⟨row, rowMember, tokenEq⟩ := missingDiagnostics_contains built member metadata keyView valueView within
  exact ⟨row, List.mem_append_right _ rowMember, tokenEq, missingDiagnostics_rows built row rowMember⟩

/-- Extension tables contain only actual fixed rows or expanded missing rows. -/
theorem tableForRegistry_rows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (member : row ∈ table.additional) :
    row ∈ program.fixed ∨ MissingRow registry program.missing row := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst table
  rcases List.mem_append.mp member with fixed | missing
  · exact .inl fixed
  · exact .inr (missingDiagnostics_rows built row missing)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
