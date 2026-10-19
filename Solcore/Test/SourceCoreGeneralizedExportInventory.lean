import Solcore.Test.SourceCoreGeneralizedExportFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! Every actual cached position receives its original static input and issued
Header. The ordered inventory is complete; selection never removes other rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure CachedObservation (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) where
  signature : ProgramFunctionSignature
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  declaration : named.specialized.declaration = signature.id
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  parameters : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false

def observeCached (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) :
    IO (CachedObservation fixture named) := do
  match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (named.specialized.declaration = signature.id)) with
  | none => throw (IO.userError "generalized export cached original signature")
  | some signature =>
    let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "generalized export cached substitution"
    let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "generalized export cached return"
    let ⟨parameters⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true)
      "generalized export cached parameters"
    return ⟨signature, List.mem_of_find?_eq_some found,
      by simpa only [decide_eq_true_eq] using List.find?_some found,
      substitution, ordinary, by
        intro binder member
        have admitted := List.all_eq_true.mp parameters binder member
        cases marker : binder.comptime <;> simp_all⟩

inductive ObservedCache (fixture : CompiledFixture) : List SourceCoreGeneralFunctions.Function → Type where
  | nil : ObservedCache fixture []
  | cons {named rest} (observation : CachedObservation fixture named) (tail : ObservedCache fixture rest) :
      ObservedCache fixture (named :: rest)

def observeCache (fixture : CompiledFixture) :
    (functions : List SourceCoreGeneralFunctions.Function) → IO (ObservedCache fixture functions)
  | [] => pure .nil
  | named :: rest => return .cons (← observeCached fixture named) (← observeCache fixture rest)

theorem ObservedCache.at_slot {fixture : CompiledFixture} {functions : List SourceCoreGeneralFunctions.Function}
    (cache : ObservedCache fixture functions) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : functions[index]? = some named) : Nonempty (CachedObservation fixture named) := by
  induction cache generalizing index with
  | nil => cases selected
  | cons observation tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero] at selected; cases selected; exact ⟨observation⟩
    | succ index => exact ih selected

structure WholeInventory (fixture : ProfiledFixture) where
  inputs : List (Input fixture.original.recipe.compiled)
  rows : Inventory inputs
  positions : inputs.map (fun input => input.prepared.index) =
    (List.finRange fixture.original.recipe.compiled.indexed.base.functions.length).map Fin.val

theorem WholeInventory.distinct {fixture : ProfiledFixture} (whole : WholeInventory fixture) :
    (whole.inputs.map (fun input => input.prepared.index)).Nodup := by
  rw [whole.positions]
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun different equal => different (Fin.ext equal)) (List.nodup_finRange _)

theorem WholeInventory.complete {fixture : ProfiledFixture} (whole : WholeInventory fixture)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named) :
    ∃ input ∈ whole.inputs, input.prepared.index = index ∧ input.prepared.named = named := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have member : index ∈ whole.inputs.map (fun input => input.prepared.index) := by
    rw [whole.positions]
    exact List.mem_map.mpr ⟨⟨index, bound⟩, List.mem_finRange _, rfl⟩
  obtain ⟨input, present, same⟩ := List.mem_map.mp member
  have found := input.prepared.selected
  rw [same] at found
  exact ⟨input, present, same, Option.some.inj (found.symm.trans selected)⟩

/-- The full list of actual slots is traversed directly. All ordinary source
facts are finite observations, while origin and Header issuance come from the
real preparation and original declarative program typing. -/
theorem ProfiledFixture.inventory (fixture : ProfiledFixture)
    (cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (WholeInventory fixture) := by
  classical
  let functions := fixture.original.recipe.compiled.indexed.base.functions
  have available : ∀ position : Fin functions.length, ∃ input : Input fixture.original.recipe.compiled,
      input.prepared.index = position.val ∧ input.prepared.named = functions[position.val] := by
    intro position
    have selected : functions[position.val]? = some functions[position.val] := List.getElem?_eq_getElem position.isLt
    obtain ⟨observation⟩ := cache.at_slot selected
    have origin := SelectedCompilationCatalog.ordinary_origin fixture.original.recipe.compiled
      wellFormed.signatures (RecursiveNamedPreparedFinalPlanOrigins.final_member _ selected rfl)
      observation.member observation.declaration
    have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
        functions[position.val].specialized.parameterSubstitution := by
      rw [observation.substitution]
      intro name value found
      cases found
    obtain ⟨input, _row, slot, named⟩ := SelectedCompilationCatalog.of_cached fixture.original.recipe.compiled
      wellFormed.signatures selected origin range observation.ordinary observation.parameters
    exact ⟨input, slot, named⟩
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := (List.finRange functions.length).map choose
  obtain ⟨rows⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.inventory wellFormed inputs
  refine ⟨⟨inputs, rows, ?_⟩⟩
  simp only [inputs, List.map_map]
  exact List.map_congr_left (fun position _ => (chosen position).1)

structure SelectedInventory {fixture : ProfiledFixture} (whole : WholeInventory fixture)
    (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  retained : Inventory.HasRow packet whole.rows

theorem WholeInventory.select {fixture : ProfiledFixture} (whole : WholeInventory fixture)
    (row : Row fixture.original) : Nonempty (SelectedInventory whole row) := by
  obtain ⟨index, named, selected, same⟩ := RecursiveNamedPublicSpecializationMeaning.cached_row
    fixture.original.recipe.compiled row.member
  obtain ⟨input, present, _slot, selectedNamed⟩ := whole.complete selected
  obtain ⟨packet, retained⟩ := whole.rows.row_at input present
  exact ⟨⟨input, input.prepared.same.symm.trans ((congrArg (·.specialized) selectedNamed).trans same), packet, retained⟩⟩

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {whole : WholeInventory fixture}
    {row : Row fixture.original} (selected : SelectedInventory whole row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {whole : WholeInventory fixture}
    {row : Row fixture.original} (selected : SelectedInventory whole row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) (key : root.key = row.original.key) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers whole.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, namedKey, rootKey, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have selectedKey : selected.input.prepared.named.signature.key = row.original.key := by
    rw [CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key _ selected.input.prepared.selected,
      selected.input.prepared.same, selected.original]
  have keyEq : named.signature.key = selected.input.prepared.named.signature.key :=
    namedKey.trans (rootKey.symm.trans (key.trans selectedKey.symm))
  have actualSlot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot _ atIndex
  have selectedSlot := selected.input.slot
  unfold CallableNamedMetadata.Slot at actualSlot selectedSlot
  rw [keyEq] at actualSlot
  have sameSlot := congrArg (fun entries => entries.head?) (selectedSlot.symm.trans actualSlot)
  have indexEq : selected.input.prepared.index = index := congrArg Prod.snd (Option.some.inj sameSlot)
  have actualNamed := selected.input.prepared.selected
  rw [indexEq] at actualNamed
  have same : selected.input.prepared.named = named := Option.some.inj (actualNamed.symm.trans atIndex)
  refine ⟨Inventory.header_member selected.retained, entry, present,
    ⟨named, index, found, namedKey, rootKey, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [same, indexEq] using found

theorem WholeInventory.length {fixture : ProfiledFixture} (whole : WholeInventory fixture) :
    whole.inputs.length = 3 := by
  have same := congrArg List.length whole.positions
  simpa only [List.length_map, List.length_finRange, fixture.cached] using same

theorem SelectedInventory.source_eq {fixture : ProfiledFixture} {whole : WholeInventory fixture}
    {row : Row fixture.original} (selected : SelectedInventory whole row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def cacheProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _cache ← observeCache fixture.original fixture.original.recipe.compiled.indexed.base.functions
  IO.println "GENERALIZED_EXPORT_STATIC_CACHE: originals3/cache3/profile3/observed3"

end Tests.SourceCoreGeneralizedExport
