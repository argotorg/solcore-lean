import Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore

/-! The caller deliberately supplies a reference to an old heap cell. The
closed initializer still appends helper cells without modifying that old cell. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataEqualityStoreProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEqualityInitializationStore

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked) :
    ∃ body captured administrative required,
      administrative.length = checked.catalog.entries.length ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression [.cellRef .integer 0] [.integer 900]) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) (.integer 900 :: administrative) := by
  have environment : RuntimeEnvironmentHasTypes [.integer] [.cellRef .integer 0] [.cell .integer] checked.catalog.definitions :=
    .cons (.cellRef rfl) .nil
  have store : RuntimeStoreHasTypes [.integer] [.integer 900] checked.catalog.definitions := {
    length_eq := rfl
    lookup := by
      intro location type found
      cases location with
      | zero => cases found; exact ⟨_, rfl, .integer⟩
      | succ location => simp at found
  }
  obtain ⟨body, captured, administrative, _, length, _, _, _, ⟨required, runs⟩, _⟩ :=
    prepared_run_extends prepared environment store
  exact ⟨body, captured, administrative, required, length, runs⟩

end Tests.SourceCoreDataEqualityStoreProofs
