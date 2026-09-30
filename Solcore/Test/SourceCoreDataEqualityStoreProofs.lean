import Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled

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

/-- A completed preparation authenticates exact code/capture contents, not
just function tags. The first helper captures no installation Unit binder. -/
example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (firstBody : Expr) (first : prepared.bodies[0]? = some firstBody)
    (fuel : Nat) (value : Value) (finalStore : Store)
    (ran : runStateful fuel (.initial prepared.expression [.cellRef .integer 0] [.integer 900]) = .done value finalStore) :
    finalStore.read? 1 = some (.inRight .unit
      (DataEqualityInstalled.helper (DataEqualityInstalled.allocatedEnvironment checked.catalog 1 [.cellRef .integer 0]) firstBody 0)) := by
  obtain ⟨_, _, installed⟩ := DataEqualityInstalled.prepared_completed_installed prepared ran
  exact installed 0 firstBody first

/-- Later closures retain both their shifted bodies and previous write-result
binders; exact initialization does not collapse these captures to one template. -/
example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (secondBody : Expr) (second : prepared.bodies[1]? = some secondBody)
    (fuel : Nat) (value : Value) (finalStore : Store)
    (ran : runStateful fuel (.initial prepared.expression [] []) = .done value finalStore) :
    finalStore.read? 1 = some (.inRight .unit
      (.closure (.product (.namedData ⟨1⟩) (.namedData ⟨1⟩)) .bool
        (secondBody.rename (DataEqualityInstalled.offset 1).lift)
        (.unit :: DataEqualityInstalled.allocatedEnvironment checked.catalog 0 []))) := by
  obtain ⟨_, _, installed⟩ := DataEqualityInstalled.prepared_completed_installed prepared ran
  simpa [DataEqualityInstalled.helper, DataEqualityInstalled.captured] using installed 1 secondBody second

end Tests.SourceCoreDataEqualityStoreProofs
