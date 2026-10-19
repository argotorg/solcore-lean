import Solcore.Test.SourceCoreGeneralizedExportInventory
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles

/-! Selected factory output profiles are observed on actual cached rows. The
complete three-row source, compilation and ordinary profile remain intact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure MaterializedRow (fixture : CompiledFixture) (row : Row fixture) where
  named : SourceCoreGeneralFunctions.Function
  index : Nat
  selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named
  original : named.specialized = row.original
  profile : CellAwareMaterializedNamedProfiles.Entry fixture.recipe.compiled.indexed named

private theorem original_of_key {fixture : CompiledFixture} {row : Row fixture}
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named)
    (key : named.signature.key = row.original.key) : named.specialized = row.original := by
  obtain ⟨otherIndex, other, found, same⟩ :=
    RecursiveNamedPublicSpecializationMeaning.cached_row fixture.recipe.compiled row.member
  have actual := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record fixture.recipe.compiled selected
  have original := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record fixture.recipe.compiled found
  have otherKey := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key fixture.recipe.compiled found
  rw [same] at otherKey
  rw [otherKey, same] at original
  rw [key] at actual
  exact Except.ok.inj (actual.symm.trans original)

def observeMaterializedRow (fixture : CompiledFixture) (row : Row fixture) : IO (MaterializedRow fixture row) := do
  match found : fixture.recipe.compiled.indexed.base.functions.zipIdx.find?
      (fun pair : SourceCoreGeneralFunctions.Function × Nat => decide (pair.1.signature.key = row.original.key)) with
  | none => throw (IO.userError "materialized factory actual cached row")
  | some (named, index) =>
    match accepted : CellAwareMaterializedNamedProfiles.entry? fixture.recipe.compiled.indexed named with
    | none => throw (IO.userError "materialized factory actual output profile")
    | some profile =>
      have selected := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
      have key : named.signature.key = row.original.key := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      return ⟨named, index, selected, original_of_key selected key, profile⟩

theorem MaterializedRow.named_eq {fixture : ProfiledFixture} {whole : WholeInventory fixture}
    {row : Row fixture.original} (observed : MaterializedRow fixture.original row)
    (selected : SelectedInventory whole row) : observed.named = selected.input.prepared.named := by
  have leftKey := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key
    fixture.original.recipe.compiled observed.selected
  have rightKey := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key
    fixture.original.recipe.compiled selected.input.prepared.selected
  have sameKey : observed.named.signature.key = selected.input.prepared.named.signature.key := by
    rw [leftKey, rightKey, observed.original, selected.input.prepared.same, selected.original]
  have leftSlot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
    fixture.original.recipe.compiled observed.selected
  have rightSlot := selected.input.slot
  unfold CallableNamedMetadata.Slot at leftSlot rightSlot
  rw [sameKey] at leftSlot
  have slots := congrArg (fun entries => entries.head?) (leftSlot.symm.trans rightSlot)
  have indexEq : observed.index = selected.input.prepared.index := congrArg Prod.snd (Option.some.inj slots)
  have found := observed.selected
  rw [indexEq] at found
  exact Option.some.inj (found.symm.trans selected.input.prepared.selected)

def MaterializedRow.for_selected {fixture : ProfiledFixture} {whole : WholeInventory fixture}
    {row : Row fixture.original} (observed : MaterializedRow fixture.original row)
    (selected : SelectedInventory whole row) :
    CellAwareMaterializedNamedProfiles.Entry fixture.original.recipe.compiled.indexed selected.input.prepared.named :=
  observed.named_eq selected ▸ observed.profile

def materializedProfileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let make ← observeRow fixture.original "make"
  let capture ← observeRow fixture.original "capture"
  let _makeProfile ← observeMaterializedRow fixture.original make
  let _captureProfile ← observeMaterializedRow fixture.original capture
  IO.println "GENERALIZED_EXPORT_MATERIALIZED_PROFILE: originals3/cache3/profile3/make+capture"

end Tests.SourceCoreGeneralizedExport
