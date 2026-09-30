import Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates

/-! Proof consumers join real initialization and actual scalar/product
comparison compilation to independent source equality. The catalog may contain
unrelated recursive helpers; comparison performs no extra allocations. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataEqualityScalarProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEquality DataEqualityScalarCertificates DataPatternValues

private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction

private def leftSource : Dynamic.Value := .product (.bool true) (.integer (-9))
private def leftValue : Core.Value := .pair (.bool true) (.integer (-9))
private def rightSource : Dynamic.Value := .product (.bool false) (.integer (-9))
private def rightValue : Core.Value := .pair (.bool false) (.integer (-9))

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (type : prepared.type = .product .bool .integer) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial
        (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 2))))
        [leftValue, rightValue] store) =
        .done (.bool false) (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length [leftValue, rightValue]) prepared.bodies) := by
  have profile : ScalarType prepared.type := type ▸ (.product .bool .integer)
  have leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  have rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  obtain ⟨result, meaning, evaluates⟩ := prepared_compare_preserves prepared profile noIdentities
    (sourceLeft := leftSource) (sourceRight := rightSource)
    (.product (.bool _) (.integer _)) (.product (.bool _) (.integer _)) leftTyped rightTyped
    [leftValue, rightValue] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have falseResult : result = false := by
    cases result with
    | false => rfl
    | true => have impossible := (meaning.mp rfl).1; cases impossible
  subst result
  simpa [Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluates

example (checked : SourceCoreDataCatalog.Checked) (prepared : Prepared checked)
    (type : prepared.type = .product .bool .integer) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial
        (.letE prepared.expression (.apply (.var 0) (.pair (.var 1) (.var 1))))
        [leftValue] store) =
        .done (.bool true) (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length [leftValue]) prepared.bodies) := by
  have profile : ScalarType prepared.type := type ▸ (.product .bool .integer)
  have typed : ValueHasType leftValue prepared.type checked.catalog.definitions := type ▸ (.pair .bool .integer)
  obtain ⟨result, meaning, evaluates⟩ := prepared_compare_preserves prepared profile noIdentities
    (sourceLeft := leftSource) (sourceRight := leftSource)
    (.product (.bool _) (.integer _)) (.product (.bool _) (.integer _)) typed typed
    [leftValue] store (.var 0) (.var 0) (.var rfl) (.var rfl)
  have trueResult : result = true := meaning.mpr ⟨rfl, .product (.bool _) (.integer _)⟩
  subst result
  simpa [Expr.weakenAt] using evaluation_runStateful_complete_with_sufficient_fuel evaluates

end Tests.SourceCoreDataEqualityScalarProofs
