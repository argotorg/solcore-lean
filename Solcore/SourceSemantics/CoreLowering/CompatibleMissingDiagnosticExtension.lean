import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges

/-! Rebuilding missing-value diagnostics preserves the exact first public row
for every already issued token, even though new rows interleave by site. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticRows
open CompatiblePlaceMissingDiagnosticAssociation

private abbrev Row := Word × Diagnostic

private def candidate (site : MissingSite) (token : Word)
    (entry : SourceCoreRawMetadata.Metadata × Nat) : Option Row :=
  match entry.1 with
  | .mapping key value =>
      if SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
          SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType ∧
          token.val = site.base.val + entry.2 + 1 then
        some (token, { error := .typeMismatch value none, site := site.site, span := some site.span })
      else none
  | _ => none

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {out : β}
    (accepted : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem duplicate_find (rows : List Row) (row : Row) (token : Word) :
    (if rows.any (fun previous => decide (previous.1 = row.1)) then rows else rows ++ [row]).find?
        (fun found => decide (found.1 = token)) =
      (rows.find? (fun found => decide (found.1 = token))).or
        (if row.1 = token then some row else none) := by
  by_cases same : row.1 = token
  · subst token
    by_cases present : rows.any (fun previous => decide (previous.1 = row.1)) = true
    · obtain ⟨old, member, equal⟩ := List.any_eq_true.mp present
      have someFound : (rows.find? (fun found => decide (found.1 = row.1))).isSome :=
        List.find?_isSome.mpr ⟨old, member, equal⟩
      cases found : rows.find? (fun found => decide (found.1 = row.1)) with
      | none => simp [found] at someFound
      | some selected => simp [present, found]
    · simp [present, List.find?_append]
  · split <;> simp [same]

private theorem missing_find {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List Row} (accepted : missingDiagnostics registry sites = .ok rows) (token : Word) :
    rows.find? (fun row => decide (row.1 = token)) =
      sites.findSome? (fun site => registry.entries.zipIdx.findSome? (candidate site token)) := by
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    cases Except.ok.inj finished
    apply CompatibleMemberCertificates.forIn_preserves loop (fun seen output =>
      output.find? (fun row => decide (row.1 = token)) =
        seen.findSome? (fun site => registry.entries.zipIdx.findSome? (candidate site token)))
    · rfl
    · intro seen site remaining state outcome _ previous ran
      obtain ⟨updated, inner, finished⟩ := bind_ok ran
      refine ⟨updated, (Except.ok.inj finished).symm, ?_⟩
      have innerResult : updated.find? (fun row => decide (row.1 = token)) =
          (state.find? (fun row => decide (row.1 = token))).or
            (registry.entries.zipIdx.findSome? (candidate site token)) := by
        apply CompatibleMemberCertificates.forIn_preserves inner (fun seen output =>
          output.find? (fun row => decide (row.1 = token)) =
            (state.find? (fun row => decide (row.1 = token))).or
              (seen.findSome? (candidate site token)))
        · simp
        · intro seen entry remaining current result _ previous ran
          obtain ⟨metadata, index⟩ := entry
          dsimp only at ran
          cases metadata with
          | proxy inner | constructor inner =>
            refine ⟨current, (Except.ok.inj ran).symm, ?_⟩
            simpa [candidate] using previous
          | mapping key value =>
            dsimp only at ran
            split at ran
            · rename_i matched
              have views : SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
                  SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using matched
              obtain ⟨reason, generated, finished⟩ := bind_ok ran
              have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
                change (match Word.ofNat? (site.base.val + index + 1) with
                  | some value => Except.ok value | none => Except.error Error.reasonSpaceExhausted) = .ok reason at generated
                split at generated
                · cases generated; assumption
                · cases generated
              have number : reason.val = site.base.val + index + 1 := by
                unfold Word.ofNat? at converted
                split at converted
                · exact congrArg Fin.val (Option.some.inj converted).symm
                · cases converted
              let row : Row := (reason, {error := .typeMismatch value none, site := site.site, span := some site.span})
              have candidateEq : candidate site token (.mapping key value, index) =
                  (if reason = token then some row else none) := by
                have iffEq : token.val = site.base.val + index + 1 ↔ reason = token := by
                  constructor
                  · intro eq; apply Fin.ext; omega
                  · intro eq; simpa [eq] using number
                simp [candidate, views.1, views.2, iffEq, row]
                split
                · rename_i same; simp [same]
                · rfl
              have nextFind := duplicate_find current row token
              split at finished
              · rename_i present
                refine ⟨current, (Except.ok.inj finished).symm, ?_⟩
                have nextFind := nextFind
                simp only [row, present, ↓reduceIte] at nextFind
                rw [nextFind, previous]
                simp only [List.findSome?_append, List.findSome?_singleton,
                  candidateEq, Option.or_assoc]
                rfl
              · rename_i absent
                refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
                have nextFind := nextFind
                simp only [row, absent, Bool.false_eq_true, ↓reduceIte] at nextFind
                rw [nextFind, previous]
                simp only [List.findSome?_append, List.findSome?_singleton,
                  candidateEq, Option.or_assoc]
                rfl
            · rename_i unmatched
              have notViews : ¬ (SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
                  SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType) := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using unmatched
              refine ⟨current, (Except.ok.inj ran).symm, ?_⟩
              have noCandidate : candidate site token (.mapping key value, index) = none := by
                simp only [candidate]
                split
                · rename_i matched; exact False.elim (notViews ⟨matched.1, matched.2.1⟩)
                · rfl
              simpa [noCandidate] using previous
      simpa only [List.findSome?_append, List.findSome?_singleton, previous] using innerResult
  · cases accepted

private theorem findSome_congr {α β : Type} (items : List α) (left right : α → Option β)
    (same : ∀ item, item ∈ items → left item = right item) :
    items.findSome? left = items.findSome? right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.findSome?_cons, List.findSome?_cons, same head (by simp)]
    cases right head with
    | some => rfl
    | none => exact ih (fun item member => same item (by simp [member]))

/-- Existing tokens select exactly the same first raw diagnostic after a genuine
metadata extension. Newly inserted site-major rows cannot shadow the old token. -/
theorem missingDiagnostics_find_preserved
    {before after : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends before after)
    {sites : List MissingSite} (ranges : Ranges before.limits.maxEntries sites)
    {oldRows newRows : List Row}
    (oldBuilt : missingDiagnostics before sites = .ok oldRows)
    (newBuilt : missingDiagnostics after sites = .ok newRows)
    {token : Word} {row : Row}
    (found : oldRows.find? (fun selected => decide (selected.1 = token)) = some row) :
    newRows.find? (fun selected => decide (selected.1 = token)) = some row := by
  have origin := missingDiagnostics_rows oldBuilt row (List.mem_of_find?_eq_some found)
  have same : row.1 = token := of_decide_eq_true (List.find?_some (p := fun selected : Row => decide (selected.1 = token)) found)
  obtain ⟨original, originalMember, originalIndex, originalKey, originalValue,
    originalStored, _, _, converted, _⟩ := origin
  have tokenNumber : token.val = original.base.val + originalIndex + 1 := by
    unfold Word.ofNat? at converted
    split at converted
    · have number := congrArg Fin.val (Option.some.inj converted).symm
      simpa only [same] using number
    · cases converted
  have originalBound : originalIndex < before.entries.length := by
    have bounded := List.snd_lt_of_mem_zipIdx originalStored
    simpa only [Nat.add_zero] using bounded
  have beforeBudget := missingDiagnostics_budget oldBuilt
  have afterBudget := missingDiagnostics_budget newBuilt
  rw [extension.limits] at afterBudget
  change before.entries.length ≤ before.limits.maxEntries at beforeBudget
  change after.entries.length ≤ before.limits.maxEntries at afterBudget
  obtain ⟨suffix, appended⟩ := extension.suffix
  have suffixNoMatch : ∀ site, site ∈ sites →
      (suffix.zipIdx before.entries.length).findSome? (candidate site token) = none := by
    intro site member
    apply List.findSome?_eq_none_iff.mpr
    intro entry stored
    have lower := List.le_snd_of_mem_zipIdx stored
    have upper := List.snd_lt_of_mem_zipIdx stored
    have afterLength : after.entries.length = before.entries.length + suffix.length := by simp [appended]
    have numeric : token.val ≠ site.base.val + entry.2 + 1 := by
      intro equal
      rcases ranges.separated original originalMember site member with bases | first | last
      · have bases := congrArg Fin.val bases
        omega
      · omega
      · omega
    obtain ⟨metadata, index⟩ := entry
    cases metadata with
    | proxy inner | constructor inner => rfl
    | mapping key value =>
      dsimp only [candidate]
      split
      · rename_i matched
        exact False.elim (numeric matched.2.2)
      · rfl
  have scans : sites.findSome? (fun site => after.entries.zipIdx.findSome? (candidate site token)) =
      sites.findSome? (fun site => before.entries.zipIdx.findSome? (candidate site token)) := by
    apply findSome_congr
    intro site member
    rw [appended, List.zipIdx_append, List.findSome?_append]
    simp only [Nat.zero_add, suffixNoMatch site member, Option.or_none]
  rw [missing_find newBuilt token, scans, ← missing_find oldBuilt token]
  exact found

end Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
