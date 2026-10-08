import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
import Solcore.SourceSemantics.CoreLowering.CompatiblePathMissingTerminal

/-! Actual expanded rows are interpreted using their owning ranges and raw
metadata. A duplicate row may retain a different public span; its error is
identified only by the same nonwrapping header in the authentic registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticRows

/-- Numeric separation is a static receipt for the actual issued inventory. -/
structure Ranges (capacity : Nat) (sites : List MissingSite) : Prop where
  reserved : ∀ site, site ∈ sites → site.base.val + capacity < wordModulus
  separated : ∀ left, left ∈ sites → ∀ right, right ∈ sites →
    left.base = right.base ∨ left.base.val + capacity < right.base.val ∨
      right.base.val + capacity < left.base.val

/-- Same-token rows in separated real ranges have the same raw owning header,
and hence the same semantic error. No requested span is reconstructed. -/
theorem row_error {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    (ranges : Ranges registry.limits.maxEntries sites)
    (budget : registry.length ≤ registry.limits.maxEntries)
    {site : MissingSite} (member : site ∈ sites)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    {row : Word × Diagnostic} (origin : MissingRow registry sites row)
    (same : row.1 = site.base.add header) : row.2.error = .typeMismatch rawValue none := by
  obtain ⟨actual, actualMember, actualKey, actualValue, actualHeader, actualMetadata,
    _, _, actualToken, _, actualDiagnostic⟩ := origin.metadata
  have leftBound := Nat.le_trans (metadata_headerBound metadata) budget
  have rightBound := Nat.le_trans (metadata_headerBound actualMetadata) budget
  have leftReserved := ranges.reserved site member
  have rightReserved := ranges.reserved actual actualMember
  have tokens : site.base.add header = actual.base.add actualHeader := same.symm.trans actualToken
  rcases ranges.separated site member actual actualMember with bases | before | after
  · have numbers := congrArg Fin.val tokens
    rw [token_nonWrapping _ _ _ leftReserved leftBound,
      token_nonWrapping _ _ _ rightReserved rightBound] at numbers
    have headers : header = actualHeader := by
      apply Fin.ext
      have bases := congrArg Fin.val bases
      omega
    have sameMetadata := Option.some.inj (metadata.lookup.symm.trans (headers.symm ▸ actualMetadata.lookup))
    have sameValue : rawValue = actualValue := (SourceCoreRawMetadata.Metadata.mapping.inj sameMetadata).2
    simp only [actualDiagnostic, sameValue]
  · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ leftReserved rightReserved leftBound rightBound before tokens)
  · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ rightReserved leftReserved rightBound leftBound after tokens.symm)

/-- A fixed row outside the selected reserved interval cannot shadow its
positive authenticated header. -/
theorem fixed_different {registry : SourceCoreRawMetadata.Registry} {site : MissingSite}
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (budget : registry.length ≤ registry.limits.maxEntries)
    (reserved : site.base.val + registry.limits.maxEntries < wordModulus)
    {row : Word × Diagnostic}
    (separate : row.1.val ≤ site.base.val ∨ site.base.val + registry.limits.maxEntries < row.1.val) :
    row.1 ≠ site.base.add header := by
  intro same
  have positive : 0 < header.val := by
    have nonzero := metadata.nonzero
    by_cases zero : header.val = 0
    · exact False.elim (nonzero (Fin.ext zero))
    · omega
  have bounded := Nat.le_trans (metadata_headerBound metadata) budget
  have number := congrArg Fin.val same
  rw [token_nonWrapping _ _ _ reserved bounded] at number
  rcases separate with before | after <;> omega

/-- Decode the actual first matching row. Coverage, range separation and fixed
row separation are static table facts; no universal fault relation is used. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    (ranges : Ranges registry.limits.maxEntries program.missing)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (fixed : ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + registry.limits.maxEntries < row.1.val)
    (positive : site.base.add header ≠ Word.zero)
    (ordinary : site.base.add header ≠ table.escapedReason) :
    ∃ diagnostic, table.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  have budget := tableForRegistry_budget accepted
  obtain ⟨row, rowMember, same, _⟩ := tableForRegistry_contains accepted member metadata keyView valueView
    (ranges.reserved site member)
  have covered : (table.additional.find? (fun candidate => decide (candidate.1 = site.base.add header))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨row, rowMember, by simp only [same, decide_true]⟩
  cases found : table.additional.find? (fun candidate => decide (candidate.1 = site.base.add header)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at covered
  | some selected =>
    have selectedMember := List.mem_of_find?_eq_some found
    have selectedToken : selected.1 = site.base.add header := of_decide_eq_true (List.find?_some (p := fun candidate : Word × Diagnostic => decide (candidate.1 = site.base.add header)) found)
    have error : selected.2.error = .typeMismatch rawValue none := by
      rcases tableForRegistry_rows accepted selectedMember with old | missing
      · exact False.elim (fixed_different metadata budget (ranges.reserved site member) (fixed selected old) selectedToken)
      · exact row_error ranges budget member metadata missing selectedToken
    exact ⟨selected.2, by simp only [SourceCoreFaultSites.Table.diagnostic?, positive, ordinary, found, if_false], error⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation
