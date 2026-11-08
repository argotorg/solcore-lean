import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.MaterializedBodies
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.Test.SourceSemantics.CoreLowering.Selected.GeneralizedSource
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHandles
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicForward
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.AcceptedPublicRoots
import Solcore.SourceSemantics.CoreLowering.AcceptedExpressions
import Solcore.SourceSemantics.CoreLowering.AcceptedShapes
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicRoots
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Interleaved

/-!
# Generalized export tests

Export of generalized closures: accepted bodies, handles, history and selected registries.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportProbe
/-! Runtime coverage of returned generalized instances and retained captures.
Independent Source/public correspondence is established by separate proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(flag: Bool) returns (function(Word) returns (Word), function(Bool) returns (Bool)) { let f = lam(value) { return value; }; return (f, f); }",
    "function capture(seed: Word) returns (function(Bool) returns (Word)) { let f = lam(value) { return seed; }; return f; }",
    "function tick(flag: Bool) returns (Bool) { return flag; }" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: output {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: fuel exhausted")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

def probe : IO Unit := do
  let program ← get "check generalized exports" (checkProgram workspace options.checkingFuel)
  let source ← get "compile generalized exports" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "generalized export cache absent")
  require (program.functions.length == 3 && cached.indexed.base.functions.length == 3) "complete export cache changed"
  let some _profiles := CellAwareNamedProgramProfiles.profile? cached.indexed
    | throw (IO.userError "generalized export complete profile rejected")
  let recipe ← get "prepare generalized exports" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some make := recipe.roots[0]? | throw (IO.userError "make root absent")
  let some capture := recipe.roots[1]? | throw (IO.userError "capture root absent")
  let some tick := recipe.roots[2]? | throw (IO.userError "tick root absent")
  let facade ← get "public generalized exports" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let pair ← succeeded "make" (← initial.run make.key [.bool true] runOptions)
  let .product (.function first) (.function second) := pair.value
    | throw (IO.userError "generalized export pair shape")
  let saved ← succeeded "capture" (← pair.session.run capture.key [.word (word 29)] runOptions)
  let .function captured := saved.value | throw (IO.userError "generalized captured handle shape")
  let intervening ← succeeded "tick" (← saved.session.run tick.key [.bool false] runOptions)
  require (intervening.value == .bool false) "intervening call result"
  let firstCall ← succeeded "Word handle" (← intervening.session.invokePacked first (.word (word 47)) runOptions)
  require (firstCall.value == .word (word 47)) "generalized Word result"
  let secondCall ← succeeded "Bool handle" (← firstCall.session.invokePacked second (.bool true) runOptions)
  require (secondCall.value == .bool true) "generalized Bool result"
  let capturedCall ← succeeded "captured handle" (← secondCall.session.invokePacked captured (.bool false) runOptions)
  require (capturedCall.value == .word (word 29)) "generalized captured value changed"
  let repeatCall ← succeeded "repeated Word handle" (← capturedCall.session.invokePacked first (.word (word 61)) runOptions)
  require (repeatCall.value == .word (word 61)) "repeated generalized handle changed"
  IO.println s!"GENERALIZED_EXPORT_HEAPS: {[initial.heapSize,pair.session.heapSize,saved.session.heapSize,intervening.session.heapSize,firstCall.session.heapSize,secondCall.session.heapSize,capturedCall.session.heapSize,repeatCall.session.heapSize]}"
  IO.println "GENERALIZED_EXPORT_FULL_INVENTORY: originals3/cache3/profile3"
  IO.println "GENERALIZED_EXPORT_PROBE_PASS"

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "generalized export artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "generalized export original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized export original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized export global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized export substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized export ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized export ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "generalized export unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 3
  cached : original.recipe.compiled.indexed.base.functions.length = 3
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 3)
    "generalized export complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 3)
    "generalized export complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "generalized export complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportInventory
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportMaterializedProfile
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportSource
/-! Exact original factory graphs. A generalized declaration copies the
captured input and stores its principal descriptor over the copy; returning an
instance does not execute its body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read observeRead)

structure LambdaShape (source : TypedSource) where
  input : TypedBinder
  inputType : TypeSystem.Ty
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  resultType : TypeSystem.Ty
  bodyBinder : TypedBinder
  bodyChoice : bodyBinder = parameter ∨ bodyBinder = input
  initialized : StatementNode
  lambda : ExpressionNode
  bodyReturn : StatementNode
  bodyRead : Read source bodyBinder resultType
  inputs : source.inputs = [input]
  inputScheme : input.scheme = .mono inputType
  inputCopied : CaptureBinders.copiedBinder? source input.id = some input
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) resultType⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  parameterInputDistinct : parameter.id ≠ input.id
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] resultType [bodyReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  bodyFound : source.lookupStatement? bodyReturn.id = some bodyReturn
  bodyForm : bodyReturn.form = .returnStmt (some bodyRead.node.id)

structure MakeShape (source : TypedSource) where
  principal : LambdaShape source
  inputType : principal.inputType = .bool
  resultType : principal.resultType = .variable principal.typeVariable
  identity : principal.bodyBinder = principal.parameter
  wordRead : Read source principal.binder (.function .word .word)
  boolRead : Read source principal.binder (.function .bool .bool)
  tuple : ExpressionNode
  returned : StatementNode
  roots : source.roots = [.statement principal.initialized.id, .statement returned.id]
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [wordRead.node.id, boolRead.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

structure CaptureShape (source : TypedSource) where
  principal : LambdaShape source
  inputType : principal.inputType = .word
  resultType : principal.resultType = .word
  captured : principal.bodyBinder = principal.input
  read : Read source principal.binder (.function .bool .word)
  returned : StatementNode
  roots : source.roots = [.statement principal.initialized.id, .statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

structure TickShape (source : TypedSource) where
  input : TypedBinder
  read : Read source input .bool
  returned : StatementNode
  inputs : source.inputs = [input]
  inputScheme : input.scheme = .mono .bool
  roots : source.roots = [.statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

def observeLambda (source : TypedSource) (captured : Bool)
    (bodyValue : ExpressionNode) (bodyReturn : StatementNode)
    (lambda : ExpressionNode) (initialized : StatementNode) : IO (LambdaShape source) := do
  let [input] := source.inputs | throw (IO.userError "export factory parameter count")
  let .letDecl binder _ := initialized.form | throw (IO.userError "export factory declaration")
  let .lambda [parameter] resultType _ := lambda.form | throw (IO.userError "export factory lambda")
  let [typeVariable] := binder.scheme.quantified | throw (IO.userError "export principal quantifier")
  let inputType := if captured then TypeSystem.Ty.word else .bool
  let bodyBinder := if captured then input else parameter
  let bodyRead ← observeRead source bodyBinder bodyValue resultType
  let ⟨inputs⟩ ← observed (source.inputs = [input]) "export factory input identity"
  let ⟨inputScheme⟩ ← observed (input.scheme = .mono inputType) "export factory input type"
  let ⟨inputCopied⟩ ← observed (CaptureBinders.copiedBinder? source input.id = some input) "export factory input copied"
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) resultType⟩)
    "export exact principal scheme"
  let ⟨schemeRequirements⟩ ← observed (binder.schemeRequirements = []) "export principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVariable)) "export lambda parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "export lambda requirements"
  let ⟨parameterInputDistinct⟩ ← observed (parameter.id ≠ input.id) "export distinct captured parameter"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "export declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl binder (some lambda.id)) "export declaration initializer"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "export lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] resultType [bodyReturn.id]) "export lambda original body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "export lambda raw type"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "export lambda result type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "export initializer requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "export initializer coercions"
  let ⟨bodyFound⟩ ← observed (source.lookupStatement? bodyReturn.id = some bodyReturn) "export inner return identity"
  let ⟨bodyForm⟩ ← observed (bodyReturn.form = .returnStmt (some bodyRead.node.id)) "export inner return read"
  return ⟨input,inputType,binder,parameter,typeVariable,resultType,bodyBinder,
    by cases captured <;> simp [bodyBinder],initialized,lambda,bodyReturn,bodyRead,inputs,inputScheme,inputCopied,
    scheme,schemeRequirements,parameterScheme,parameterRequirements,parameterInputDistinct,initializedFound,initializedForm,
    lambdaFound,lambdaForm,lambdaRaw,lambdaType,lambdaRequirements,lambdaCoercions,bodyFound,bodyForm⟩

def observeMake (source : TypedSource) : IO (MakeShape source) := do
  let [.expression bodyValue,.statement bodyReturn,.expression lambda,.statement initialized,
       .expression wordNode,.expression boolNode,.expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "make original complete graph")
  let principal ← observeLambda source false bodyValue bodyReturn lambda initialized
  let ⟨inputType⟩ ← observed (principal.inputType = .bool) "make Bool input"
  let ⟨resultType⟩ ← observed (principal.resultType = .variable principal.typeVariable) "make identity result"
  let ⟨identity⟩ ← observed (principal.bodyBinder = principal.parameter) "make identity binder"
  let wordRead ← observeRead source principal.binder wordNode (.function .word .word)
  let boolRead ← observeRead source principal.binder boolNode (.function .bool .bool)
  let ⟨roots⟩ ← observed (source.roots = [.statement principal.initialized.id,.statement returned.id]) "make original roots"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "make tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [wordRead.node.id,boolRead.node.id]) "make ordered instance reads"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "make tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "make tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "make return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "make return tuple"
  return ⟨principal,inputType,resultType,identity,wordRead,boolRead,tuple,returned,roots,
    tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩

def observeCapture (source : TypedSource) : IO (CaptureShape source) := do
  let [.expression bodyValue,.statement bodyReturn,.expression lambda,.statement initialized,
       .expression readNode,.statement returned] := source.nodes
    | throw (IO.userError "capture original complete graph")
  let principal ← observeLambda source true bodyValue bodyReturn lambda initialized
  let ⟨inputType⟩ ← observed (principal.inputType = .word) "capture Word input"
  let ⟨resultType⟩ ← observed (principal.resultType = .word) "capture Word result"
  let ⟨captured⟩ ← observed (principal.bodyBinder = principal.input) "capture original input binder"
  let read ← observeRead source principal.binder readNode (.function .bool .word)
  let ⟨roots⟩ ← observed (source.roots = [.statement principal.initialized.id,.statement returned.id]) "capture original roots"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "capture return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "capture return instance"
  return ⟨principal,inputType,resultType,captured,read,returned,roots,returnedFound,returnedForm⟩

def observeTick (source : TypedSource) : IO (TickShape source) := do
  let [input] := source.inputs | throw (IO.userError "tick input")
  let [.expression node,.statement returned] := source.nodes | throw (IO.userError "tick original complete graph")
  let read ← observeRead source input node .bool
  let ⟨inputs⟩ ← observed (source.inputs = [input]) "tick input identity"
  let ⟨inputScheme⟩ ← observed (input.scheme = .mono .bool) "tick input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "tick original roots"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "tick return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "tick return read"
  return ⟨input,read,returned,inputs,inputScheme,roots,returnedFound,returnedForm⟩

def LambdaShape.descriptor {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] shape.resultType [shape.bodyReturn.id]

def LambdaShape.allocatedHeap {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment)}]⟩

theorem LambdaShape.captures {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

theorem LambdaShape.initializes {source : TypedSource} (shape : LambdaShape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) {environment captured : Dynamic.Environment}
    {before middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (extended : BinderExtends source.owner context shape.binder nextContext) :
    Dynamic.StatementExecutes program context evidence source environment before shape.initialized.id
      nextContext (.fallthrough ((shape.binder.id, ⟨middle.cells.length⟩) :: environment))
      (shape.allocatedHeap context captured middle) := by
  apply Dynamic.StatementExecutes.letInitializedGeneralized
    (lookupStatement?_sound shape.initializedFound) shape.initializedForm snapshot
    (shape.captures context captured) (by rw [shape.scheme]; simp) extended
  exact .append

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportTrace
/-! Independent ordinary Source factory traces. The returned handles denote
materialized instances of the actual stored descriptor and captured environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read)

theorem LambdaShape.materializes {source : TypedSource} (shape : LambdaShape source)
    {type : TypeSystem.Ty} (readNode : Read source shape.binder type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (stored : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiated : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder type [] substitution produced) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap readNode.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) heap := by
  apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
    (lookupExpression?_sound readNode.found) readNode.form
    (by rw [readNode.requirements, readNode.coercions]; rfl)
    lookup stored descriptor fields
  · rw [readNode.raw]; exact instantiated
  · rw [readNode.coercions]; exact .nil

theorem MakeShape.instance {source : TypedSource} (shape : MakeShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.principal.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.principal.binder
      (.function type type) [] [(shape.principal.typeVariable,type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.principal.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.principal.scheme]; exact ExactSubstitution.singleton _ _
  · intro metavariable replacement member
    have same := List.mem_singleton.mp member
    cases same; exact ground
  · simp [shape.principal.scheme,shape.resultType,TypeSystem.Substitution.apply,TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates,shape.principal.schemeRequirements]; exact .nil

theorem CaptureShape.instance {source : TypedSource} (shape : CaptureShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (wellformed : SchemeWellFormed context shape.principal.binder.scheme)
    (boolean : TypeWellFormed context .bool) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.principal.binder
      (.function .bool .word) [] [(shape.principal.typeVariable,.bool)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.principal.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.principal.scheme]; exact ExactSubstitution.singleton _ _
  · intro metavariable replacement member
    have same := List.mem_singleton.mp member
    cases same; exact boolean
  · simp [shape.principal.scheme,shape.resultType,TypeSystem.Substitution.apply,TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates,shape.principal.schemeRequirements]; exact .nil

def MakeShape.value {source : TypedSource} (shape : MakeShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) : Dynamic.Value :=
  .product
    (.closure ((shape.principal.descriptor context environment).instantiate
      [(shape.principal.typeVariable,.word)] (evidence.applySubstitution [(shape.principal.typeVariable,.word)])))
    (.closure ((shape.principal.descriptor context environment).instantiate
      [(shape.principal.typeVariable,.bool)] (evidence.applySubstitution [(shape.principal.typeVariable,.bool)])))

def CaptureShape.value {source : TypedSource} (shape : CaptureShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) : Dynamic.Value :=
  .closure ((shape.principal.descriptor context environment).instantiate
    [(shape.principal.typeVariable,.bool)] (evidence.applySubstitution [(shape.principal.typeVariable,.bool)]))

theorem MakeShape.body_trace {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {context next : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    {captured : Dynamic.Environment} {middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (extended : BinderExtends source.owner context shape.principal.binder next)
    (fields : Dynamic.RuntimeContextFields context next)
    (wellformed : SchemeWellFormed next shape.principal.binder.scheme)
    (word : TypeWellFormed next .word) (boolean : TypeWellFormed next .bool) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context captured evidence))
      (shape.principal.allocatedHeap context captured middle) := by
  let heap := shape.principal.allocatedHeap context captured middle
  let locals := (shape.principal.binder.id,⟨middle.cells.length⟩) :: environment
  have allocated : Dynamic.Heap.AllocatesGeneralized middle (shape.principal.descriptor context captured)
      ⟨middle.cells.length⟩ heap := .append
  have first := shape.principal.materializes (program := program) shape.wordRead captured locals
    [(shape.principal.typeVariable,.word)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed word)
  have second := shape.principal.materializes (program := program) shape.boolRead captured locals
    [(shape.principal.typeVariable,.bool)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed boolean)
  have tuple : Dynamic.ExpressionEvaluates program next evidence source locals heap shape.tuple.id
      (shape.value context captured evidence) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
    · rw [shape.tupleForm]
      exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
        (.cons first (.cons second .nil)) (.cons (.singleton _))
    · rw [shape.tupleCoercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.cons (shape.principal.initializes evidence snapshot extended)
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tuple

theorem CaptureShape.body_trace {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {context next : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    {captured : Dynamic.Environment} {middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (extended : BinderExtends source.owner context shape.principal.binder next)
    (fields : Dynamic.RuntimeContextFields context next)
    (wellformed : SchemeWellFormed next shape.principal.binder.scheme)
    (boolean : TypeWellFormed next .bool) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context captured evidence))
      (shape.principal.allocatedHeap context captured middle) := by
  let heap := shape.principal.allocatedHeap context captured middle
  let locals := (shape.principal.binder.id,⟨middle.cells.length⟩) :: environment
  have allocated : Dynamic.Heap.AllocatesGeneralized middle (shape.principal.descriptor context captured)
      ⟨middle.cells.length⟩ heap := .append
  have materialized := shape.principal.materializes (program := program) shape.read captured locals
    [(shape.principal.typeVariable,.bool)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed boolean)
  apply Dynamic.FunctionStatementsExecute.cons (shape.principal.initializes evidence snapshot extended)
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm materialized

theorem TickShape.body_trace {source : TypedSource} (shape : TickShape source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (flag : Bool) {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.input.id location)
    (stored : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = none) (value : cell.value = some (.bool flag)) :
    Dynamic.FunctionStatementsExecute program context evidence source environment heap
      [shape.returned.id] context (.returned (.bool flag)) heap := by
  have read : Dynamic.ExpressionEvaluates program context evidence source environment heap
      shape.read.node.id (.bool flag) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.read.found)
    · rw [shape.read.form]
      exact .local (by rw [shape.read.requirements,shape.read.coercions]; rfl) lookup stored descriptor value
    · rw [shape.read.coercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm read

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportCalls
/-! Independent ordinary Source application of the exported instances. Each
call copies the instance's captured cells before binding its parameter. The
actual closure frame is static code/evidence validity; no target call is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

/-- A binding of the copied environment reads the cell its original binding read. -/
theorem copies_lookup {source : TypedSource} {environment copies : Dynamic.Environment}
    {before after : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies source environment before copies after)
    {id : Resolved.LocalId} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads before location cell) :
    ∃ found, Dynamic.Environment.LooksUp copies id found ∧ Dynamic.Heap.Reads after found cell := by
  induction copy generalizing location with
  | nil => cases lookup
  | shared _ tail ih =>
    cases lookup with
    | head => exact ⟨_, .head, tail.preserves_read read⟩
    | tail different rest =>
      obtain ⟨found, foundLookup, foundRead⟩ := ih rest read
      exact ⟨found, .tail different foundLookup, foundRead⟩
  | copied _ original allocate tail ih =>
    cases lookup with
    | head =>
      cases original.functional read
      exact ⟨_, .head, tail.preserves_read allocate.reads_new⟩
    | tail different rest =>
      obtain ⟨found, foundLookup, foundRead⟩ := ih rest (allocate.preserves_read read)
      exact ⟨found, .tail different foundLookup, foundRead⟩

theorem MakeShape.identity_applies {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    (frame : Dynamic.ClosureFrame program
      ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨copied.cells ++ [{type := (shape.principal.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.principal.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.principal.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument)
      ⟨copied.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.principal.bodyRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.principal.bodyRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.principal.bodyRead.form, shape.identity, shape.principal.bodyRead.requirements, shape.principal.bodyRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.principal.bodyRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.principal.bodyReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.principal.bodyFound))
      (by simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)) copy
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.principal.bodyFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl


theorem CaptureShape.captured_applies {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument saved : Dynamic.Value)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (capturedLookup : Dynamic.Environment.LooksUp captured shape.principal.input.id location)
    (capturedRead : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none) (capturedValue : cell.value = some saved)
    (frame : Dynamic.ClosureFrame program
      ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] saved
      ⟨copied.cells ++ [{type := (shape.principal.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.principal.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.principal.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument)
      ⟨copied.cells.length⟩ after := .append
  obtain ⟨found, foundLookup, foundRead⟩ := copies_lookup copy capturedLookup capturedRead
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.principal.bodyRead.node.id saved after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.principal.bodyRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.principal.bodyRead.form, shape.captured, shape.principal.bodyRead.requirements, shape.principal.bodyRead.coercions]
      exact .local rfl (.tail shape.principal.parameterInputDistinct foundLookup)
        (allocation.preserves_read foundRead) ordinary capturedValue
    · simp only [ExpressionNode.applySubstitution, shape.principal.bodyRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.principal.bodyReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned saved) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.principal.bodyFound))
      (by simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)) copy
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.principal.bodyFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.principal.bodyForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl


end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportSourceFirst
/-! The genuine original declaration typing supplies each exact scheme
instance before constructing the complete independent Source factory trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_,_,_,head,.nil _ _⟩
  | cons head tail => exact ⟨_,_,_,head,tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual,contains,original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

theorem LambdaShape.context_after {source : TypedSource} (shape : LambdaShape source)
    {control : ControlContext} {context next : SourceSemantics.Context} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.initialized.id next facts) :
    BinderExtends source.owner context shape.binder next ∧
      SchemeWellFormed next shape.binder.scheme ∧ Dynamic.RuntimeContextFields context next := by
  have original := form_at unique shape.initializedFound typed
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ => rw [shape.scheme] at monomorphic; cases monomorphic
  | letInitializedGeneralized _ _ _ _ extended =>
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    cases extended with
    | intro wellformed fresh =>
      exact ⟨.intro wellformed fresh, {
        binders := wellformed.scheme.binders.withLocal _ _ _
        quantified_nodup := wellformed.scheme.quantified_nodup
        body := wellformed.scheme.body.withLocal _ _ _ },fields⟩

theorem MakeShape.body_from_source {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    {captured : Dynamic.Environment} {middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context
      [shape.principal.initialized.id,shape.returned.id] final facts) :
    ∃ next, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context captured evidence))
      (shape.principal.allocatedHeap context captured middle) := by
  obtain ⟨next,_,_,first,_⟩ := head_tail typed
  obtain ⟨extended,wellformed,fields⟩ := shape.principal.context_after unique first
  exact ⟨next,shape.body_trace evidence environment before snapshot extended fields wellformed
    ⟨wellformed.binders,.builtin .word⟩ ⟨wellformed.binders,.builtin .bool⟩⟩

theorem CaptureShape.body_from_source {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    {captured : Dynamic.Environment} {middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context
      [shape.principal.initialized.id,shape.returned.id] final facts) :
    ∃ next, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context captured evidence))
      (shape.principal.allocatedHeap context captured middle) := by
  obtain ⟨next,_,_,first,_⟩ := head_tail typed
  obtain ⟨extended,wellformed,fields⟩ := shape.principal.context_after unique first
  exact ⟨next,shape.body_trace evidence environment before snapshot extended fields wellformed
    ⟨wellformed.binders,.builtin .bool⟩⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportSelectedSource
/-! Actual selected headers allocate their original inputs before independent
Source factory execution. Every selection retains the complete cache inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.result_eq (selected : SelectedInventory whole row) :
    selected.packet.header.function.resultType = row.original.function.inferredBodyType :=
  selected.packet.header.agreement.result.trans
    (congrArg (fun named => named.function.inferredBodyType) selected.header_original)

def SelectedInventory.make_shape (selected : SelectedInventory whole row)
    (original : MakeShape row.original.function.typedBody) :
    MakeShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

def SelectedInventory.capture_shape (selected : SelectedInventory whole row)
    (original : CaptureShape row.original.function.typedBody) :
    CaptureShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

def SelectedInventory.tick_shape (selected : SelectedInventory whole row)
    (original : TickShape row.original.function.typedBody) :
    TickShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

theorem SelectedInventory.factory_parameters (selected : SelectedInventory whole row)
    (shape : LambdaShape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.input] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.factory_input_types (selected : SelectedInventory whole row)
    (shape : LambdaShape selected.packet.header.function.source) :
    selected.packet.header.types = [shape.inputType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.factory_parameters shape, List.map_cons, List.map_nil,
    shape.inputScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.make_input_types (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  rw [selected.factory_input_types shape.principal, shape.inputType]

theorem SelectedInventory.capture_input_types (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source) :
    selected.packet.header.types = [.word] := by
  rw [selected.factory_input_types shape.principal, shape.inputType]

theorem SelectedInventory.tick_parameters (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.input] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.tick_input_types (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.tick_parameters shape, List.map_cons, List.map_nil,
    shape.inputScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.make_statements (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.principal.initialized.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

theorem SelectedInventory.capture_statements (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.principal.initialized.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

theorem SelectedInventory.tick_statements (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def inputHeap (before : Dynamic.Heap) (type : TypeSystem.Ty) (value : Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := type, value := some value}]⟩

def inputEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- The factory's generalized declaration copies the input cell into the next
cell, and the principal captures the copy. -/
def snapshotEnvironment (binder : TypedBinder) (before : Dynamic.Heap) (type : TypeSystem.Ty)
    (value : Dynamic.Value) : Dynamic.Environment :=
  inputEnvironment binder (inputHeap before type value)

def snapshotHeap (before : Dynamic.Heap) (type : TypeSystem.Ty) (value : Dynamic.Value) : Dynamic.Heap :=
  inputHeap (inputHeap before type value) type value

theorem LambdaShape.input_snapshot {source : TypedSource} (shape : LambdaShape source)
    (before : Dynamic.Heap) (type : TypeSystem.Ty) (value : Dynamic.Value) :
    Dynamic.EnvironmentCopies source (inputEnvironment shape.input before) (inputHeap before type value)
      (snapshotEnvironment shape.input before type value) (snapshotHeap before type value) := by
  have allocation : Dynamic.Heap.Allocates before type (some value)
      ⟨before.cells.length⟩ (inputHeap before type value) := .append
  exact .copied shape.inputCopied allocation.reads_new .append (.nil _)

theorem SelectedInventory.make_source_body (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .bool (.bool flag)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .bool (.bool flag)) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .bool (.bool flag)) (snapshotHeap before .bool (.bool flag))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (inputHeap before .bool (.bool flag)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.make_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag))
    (shape.principal.input_snapshot before _ _)
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.make_statements shape ▸ body⟩

theorem SelectedInventory.capture_source_body (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (seed : Word) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .word (.word seed)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .word (.word seed)) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .word (.word seed)) (snapshotHeap before .word (.word seed))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .word (some (.word seed))
      ⟨before.cells.length⟩ (inputHeap before .word (.word seed)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.capture_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed))
    (shape.principal.input_snapshot before _ _)
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.capture_statements shape ▸ body⟩

theorem SelectedInventory.tick_source_body (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) ∧
    Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.input before)
      (inputHeap before .bool (.bool flag)) selected.packet.header.function.body selected.packet.header.context
      (.returned (.bool flag)) (inputHeap before .bool (.bool flag)) := by
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (inputHeap before .bool (.bool flag)) := .append
  have bound : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) := by
    rw [selected.tick_parameters shape]
    exact .cons (by simpa only [shape.inputScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have body := shape.body_trace
    (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    (context := selected.packet.header.context) selected.packet.header.function.evidence
    (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) flag
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl rfl
  exact ⟨bound, selected.tick_statements shape ▸ body⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportTyping
/-! Declarative typing of all three original functions, constructed from
checked source observations. Compiler execution is not a typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

private def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}
private def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
private def factoryFacts (type : TypeSystem.Ty) : BodyFacts :=
  .cons localFacts (.singleton (returnFacts type))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  resultType : TypeSystem.Ty
  facts : BodyFacts
  factsType : facts.type = resultType
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext facts
  result : TypeSystem.Ty.productMany signature.returnTypes = resultType

private theorem roots_injective_variant {left right : List StatementId}
    (mapped : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at mapped
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at mapped
      have headEq := NodeId.statement.inj mapped.1
      have tailEq := ih mapped.2
      rw [headEq, tailEq]

theorem BodyTyping.statements_typed {signatures : ProgramSignatures} {function : CheckedFunction}
    {signature : ProgramFunctionSignature} (certificate : BodyTyping signatures function signature) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same := roots_injective_variant (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨certificate.facts, ?_, ?_⟩
  · simpa only [certificate.result] using certificate.factsType
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

def LambdaShape.initializerTyping {source : TypedSource} (shape : LambdaShape source)
    (lexical : SourceSemantics.Context)
    (inputLookup : lexical.LocalLookup shape.input.id shape.input.scheme)
    (inputRequirements : lexical.LocalSchemeRequirementsLookup shape.input.id shape.input.schemeRequirements) :
    IO (PLift (ExpressionHasType source (localSchemeInitializerContext lexical shape.binder)
      shape.lambda.id shape.binder.scheme.body)) := do
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder principal source.owner shape.parameter
  let ⟨different⟩ ← observe (shape.parameter.id ≠ shape.input.id) "export distinct captured and lambda parameter"
  have lookup : parameterContext.LocalLookup shape.bodyBinder.id shape.bodyBinder.scheme := by
    rcases shape.bodyChoice with same | same
    · rw [same]; exact extended.local_self
    · rw [same]
      exact .tail different inputLookup
  have requirements : parameterContext.LocalSchemeRequirementsLookup
      shape.bodyBinder.id shape.bodyBinder.schemeRequirements := by
    rcases shape.bodyChoice with same | same
    · rw [same]; exact extended.local_scheme_requirements_self
    · rw [same]
      exact .tail different inputRequirements
  let ⟨readTyped⟩ ← read shape.bodyRead parameterContext lookup requirements
  let ⟨returnType⟩ ← observe (shape.bodyReturn.type = shape.resultType) "export original lambda return type"
  have returned : StatementHasType source {returnType := shape.resultType} parameterContext
      shape.bodyReturn.id parameterContext (returnFacts shape.resultType) :=
    .returnValue (lookupStatement?_sound shape.bodyFound) shape.bodyForm readTyped returnType
  have parameters : MonoBindersExtend source.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme extended (.nil _)
  have form : ExpressionFormHasRawType source principal shape.lambda.form
      (.function (.variable shape.typeVariable) shape.resultType) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameters (.singleton returned)
      (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨typed⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) shape.resultType) shape.lambdaFound form
  return ⟨by simpa only [shape.scheme] using typed⟩

private def factoryInitialization {source : TypedSource} (shape : LambdaShape source)
    (lexical : SourceSemantics.Context) (result : TypeSystem.Ty)
    (inputLookup : lexical.LocalLookup shape.input.id shape.input.scheme)
    (inputRequirements : lexical.LocalSchemeRequirementsLookup shape.input.id shape.input.schemeRequirements) :
    IO (PLift (StatementHasType source {returnType := result} lexical shape.initialized.id
      (lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) localFacts) ×
      PLift (BinderExtends source.owner lexical shape.binder
        (lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements))) := do
  let ⟨initializer⟩ ← shape.initializerTyping lexical inputLookup inputRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder lexical source.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨type⟩ ← observe (shape.initialized.type = .unit) "export original generalized declaration type"
  return ⟨⟨.letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
    (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
    generalized initializer extended type⟩, ⟨extended⟩⟩

private def observeMakeTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeMake function.typedBody
  let resultType := TypeSystem.Ty.product (.function .word .word) (.function .bool .bool)
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [shape.principal.inputType]) "make signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType) "make signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.principal.input.id shape.principal.input.scheme shape.principal.input.schemeRequirements
  let ⟨inputExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.principal.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.principal.inputs, inputTypes]
    exact .cons shape.principal.inputScheme inputExtended (.nil _)
  let ⟨⟨initialized⟩,⟨extended⟩⟩ ← factoryInitialization shape.principal lexical resultType
    inputExtended.local_self inputExtended.local_scheme_requirements_self
  let finalContext := lexical.withLocal shape.principal.binder.id shape.principal.binder.scheme shape.principal.binder.schemeRequirements
  let ⟨wordTyped⟩ ← read shape.wordRead finalContext extended.local_self extended.local_scheme_requirements_self
  let ⟨boolTyped⟩ ← read shape.boolRead finalContext extended.local_self extended.local_scheme_requirements_self
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]; exact .tuple (.cons wordTyped (.cons boolTyped (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "make return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return ⟨[shape.principal.initialized.id,shape.returned.id],shape.roots,resultType,factoryFacts resultType,
    by rfl,
    lexical,finalContext,inputs,.cons initialized (.singleton returned),result⟩

private def observeCaptureTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeCapture function.typedBody
  let resultType := TypeSystem.Ty.function .bool .word
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [shape.principal.inputType]) "capture signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType) "capture signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.principal.input.id shape.principal.input.scheme shape.principal.input.schemeRequirements
  let ⟨inputExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.principal.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.principal.inputs, inputTypes]
    exact .cons shape.principal.inputScheme inputExtended (.nil _)
  let ⟨⟨initialized⟩,⟨extended⟩⟩ ← factoryInitialization shape.principal lexical resultType
    inputExtended.local_self inputExtended.local_scheme_requirements_self
  let finalContext := lexical.withLocal shape.principal.binder.id shape.principal.binder.scheme shape.principal.binder.schemeRequirements
  let ⟨typed⟩ ← read shape.read finalContext extended.local_self extended.local_scheme_requirements_self
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "capture return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm typed returnedType
  return ⟨[shape.principal.initialized.id,shape.returned.id],shape.roots,resultType,factoryFacts resultType,
    by rfl,
    lexical,finalContext,inputs,.cons initialized (.singleton returned),result⟩

private def observeTickTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeTick function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "tick signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = .bool) "tick signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.input.id shape.input.scheme shape.input.schemeRequirements
  let ⟨extended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.input
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]; exact .cons shape.inputScheme extended (.nil _)
  let ⟨typed⟩ ← read shape.read lexical extended.local_self extended.local_scheme_requirements_self
  let ⟨returnedType⟩ ← observe (shape.returned.type = .bool) "tick return type"
  have returned : StatementHasType function.typedBody {returnType := .bool} lexical
      shape.returned.id lexical (returnFacts .bool) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm typed returnedType
  return ⟨[shape.returned.id],shape.roots,.bool,.singleton (returnFacts .bool),
    by rfl,
    lexical,lexical,inputs,.singleton returned,result⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  if signature.name == "make" then observeMakeTyping signatures function signature
  else if signature.name == "capture" then observeCaptureTyping signatures function signature
  else if signature.name == "tick" then observeTickTyping signatures function signature
  else throw (IO.userError "unexpected original export function")

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportWellFormed
/-! Every original function receives its own declarative body proof. The
ordered list is the complete checked program, including the intervening tick. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

structure FunctionTyping (signatures : ProgramSignatures) (function : CheckedFunction) where
  signature : ProgramFunctionSignature
  member : signature ∈ signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping signatures function signature

inductive FunctionTypings (signatures : ProgramSignatures) : List CheckedFunction → Type where
  | nil : FunctionTypings signatures []
  | cons {function rest} (head : FunctionTyping signatures function)
      (tail : FunctionTypings signatures rest) : FunctionTypings signatures (function :: rest)

theorem FunctionTypings.at {signatures : ProgramSignatures} {functions : List CheckedFunction}
    (rows : FunctionTypings signatures functions) {function : CheckedFunction}
    (member : function ∈ functions) : Nonempty (FunctionTyping signatures function) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ ⟨head⟩
    · exact ih member

structure OriginalTyping (fixture : CompiledFixture) where
  functions : FunctionTypings fixture.recipe.compiled.sourceProgram.signatures fixture.recipe.compiled.sourceProgram.functions
  methods : fixture.recipe.compiled.sourceProgram.methods = []

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    obtain ⟨typed⟩ := original.functions.at member
    have signatureEq : signature = typed.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember typed.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans typed.owner
    subst signature
    exact typed.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeFunctions (signatures : ProgramSignatures) : (functions : List CheckedFunction) →
    IO (FunctionTypings signatures functions)
  | [] => pure .nil
  | function :: rest => do
    match found : signatures.functions.find? (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "export original signature membership")
    | some signature =>
      let body ← observeBodyTyping signatures function signature
      let tail ← observeFunctions signatures rest
      return .cons {
        signature := signature
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body } tail

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  let functions ← observeFunctions fixture.recipe.compiled.sourceProgram.signatures fixture.recipe.compiled.sourceProgram.functions
  let ⟨count⟩ ← observed (fixture.recipe.compiled.sourceProgram.methods.length = 0) "export complete original method list"
  return ⟨functions,List.length_eq_zero_iff.mp count⟩

def typingProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let original ← observeOriginalTyping fixture.original
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram) := original.wellFormed
  IO.println "GENERALIZED_EXPORT_ORIGINAL_TYPING: originals3/cache3/profile3/typed3"
  IO.println "GENERALIZED_EXPORT_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportObserved
/-! All finite observations concern the unchanged complete three-function
program. No target execution is used to construct typing or source shapes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure Observed where
  fixture : ProfiledFixture
  cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions
  make : Row fixture.original
  makeShape : MakeShape make.original.function.typedBody
  makeProfile : MaterializedRow fixture.original make
  makeResult : make.original.function.inferredBodyType = .product (.function .word .word) (.function .bool .bool)
  capture : Row fixture.original
  captureShape : CaptureShape capture.original.function.typedBody
  captureProfile : MaterializedRow fixture.original capture
  captureResult : capture.original.function.inferredBodyType = .function .bool .word
  tick : Row fixture.original
  tickShape : TickShape tick.original.function.typedBody
  tickResult : tick.original.function.inferredBodyType = .bool
  typing : OriginalTyping fixture.original
  callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observe : IO Observed := do
  let fixture ← compileProfiledFixture
  let cache ← observeCache fixture.original fixture.original.recipe.compiled.indexed.base.functions
  let make ← observeRow fixture.original "make"
  let makeProfile ← observeMaterializedRow fixture.original make
  let makeShape ← observeMake make.original.function.typedBody
  let ⟨makeResult⟩ ← observed
    (make.original.function.inferredBodyType = .product (.function .word .word) (.function .bool .bool))
    "make original result type"
  let capture ← observeRow fixture.original "capture"
  let captureProfile ← observeMaterializedRow fixture.original capture
  let captureShape ← observeCapture capture.original.function.typedBody
  let ⟨captureResult⟩ ← observed (capture.original.function.inferredBodyType = .function .bool .word)
    "capture original result type"
  let tick ← observeRow fixture.original "tick"
  let tickShape ← observeTick tick.original.function.typedBody
  let ⟨tickResult⟩ ← observed (tick.original.function.inferredBodyType = .bool) "tick original result type"
  let typing ← observeOriginalTyping fixture.original
  let ⟨callableProfile⟩ ← observed
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "generalized export actual callable profile"
  return ⟨fixture,cache,make,makeShape,makeProfile,makeResult,capture,captureShape,captureProfile,captureResult,
    tick,tickShape,tickResult,typing,callableProfile⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "generalized export bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory whole row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts whole.rows).receipts
      selected.packet.header (CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member selected.retained)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

structure InitialForward (selected : SelectedInventory whole row)
    (shape : MakeShape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    ((selected.make_shape shape).value selected.packet.header.context
      (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
    ((selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
      (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)))

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory whole row)
    (shape : MakeShape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  let actualShape := selected.make_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.make_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportAcceptedTick
/-! The accepted-body public theorems at one actual named row. `tick` of the
unchanged three-function program returns its parameter. A runtime check places
every expression node of its body in the closed expression subset and its
statement list in the supported shape; the shape covers its refined accepted
tree, and the compile receipts and the Source trace lifted through the shape
supply the remaining inputs. Together with the existing start
receipts they meet every premise of the named-row output, checkpoint and root
theorems at its first public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedNamedHeaders (index)

/-- A cache row with the key of `row`, at which the row's original body is
checked: every expression node is a closed-subset site, and its statement list
has a supported shape with those sites. -/
structure AcceptedRow (fixture : ProfiledFixture) (row : Row fixture.original) where
  named : SourceCoreGeneralFunctions.Function
  key : named.signature.key = row.original.key
  nodes : ∀ id node, row.original.function.typedBody.lookupExpression? id = some node →
    Subset fixture.original.recipe.compiled.indexed named row.original.function.typedBody id
  statements : List StatementId
  roots : row.original.function.typedBody.roots = statements.map NodeId.statement
  shape : Shape row.original.function.typedBody row.original.function.inferredBodyType
    (Subset fixture.original.recipe.compiled.indexed named row.original.function.typedBody) true statements

def observeAcceptedRow (fixture : ProfiledFixture) (row : Row fixture.original) :
    IO (AcceptedRow fixture row) := do
  match found : fixture.original.recipe.compiled.indexed.base.functions.find?
      (fun named => decide (named.signature.key = row.original.key)) with
  | none => throw (IO.userError "accepted row cache row")
  | some named =>
    let source := row.original.function.typedBody
    let some ⟨nodes⟩ := CellAwareInvocationAcceptedSubsetCheck.nodes? fixture.original.recipe.compiled.indexed
        named source
      | throw (IO.userError "accepted row outside the closed expression subset")
    let statements := source.roots.filterMap fun root =>
      match root with
      | .statement id => some id
      | .expression _ => none
    let ⟨roots⟩ ← observed (source.roots = statements.map NodeId.statement) "accepted row statement roots"
    let some ⟨shape⟩ := CellAwareInvocationAcceptedBodyShape.shape? fixture.original.recipe.compiled.indexed named
        source row.original.function.inferredBodyType (source.nodes.length + 1) true statements
      | throw (IO.userError "accepted row statement shape")
    return ⟨named, by simpa using List.find?_some found, nodes, statements, roots, shape⟩

private theorem statement_roots {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

/-- The first public call of the row, with the conclusions of the accepted-body
output theorem, the checkpoint sufficiency theorem and the checkpoint
reflection theorem. -/
structure AcceptedTick (selected : SelectedInventory whole row) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ requiredExecution requiredOutput, ∀ executionFuel outputFuel
      (outcome : SourceCoreExecution.Outcome started.artifact),
    requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
    started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
    ∃ (returned : SourceCoreExecution.Completion started.artifact)
      (actual : SourceCoreIndexedSession.Completion start.artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store),
      outcome = .succeeded returned ∧
      start.checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      returned.IndexedAt actual
  native : ∃ (value : Value) (finalStore : Store) (required : Nat),
    ∀ fuel, required ≤ fuel → start.checkpoint.NativeDone fuel value finalStore
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.bool flag] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- Every premise is an original checked or static observation, a runtime check
of the row's body, or an actual public start. The staged Source trace is lifted
from the row's independent Source execution through the checked shape. -/
theorem accepted_tick (selected : SelectedInventory whole row) (shape : TickShape row.original.function.typedBody)
    (acceptedRow : AcceptedRow fixture row) (flag : Bool)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (AcceptedTick selected flag started) := by
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  let actualShape := selected.tick_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.tick_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := selected.invocation
  have namedSame : prepared.named.specialized = row.original := prepared.same.trans selected.original
  have keyEq : acceptedRow.named.signature.key = prepared.named.signature.key :=
    acceptedRow.key.trans ((CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key _ prepared.selected).trans
      (congrArg (·.key) namedSame)).symm
  have sourceSame : CallableIndexedNamedGeneration.source prepared.named = row.original.function.typedBody :=
    congrArg (fun specialized => specialized.function.typedBody) namedSame
  have closed : CellAwareInvocationAcceptedExpressions.Closed (index prepared selected.packet.aligned) :=
    CellAwareInvocationAcceptedSubsetCheck.closed prepared.compilation _ keyEq (by rw [sourceSame]; exact acceptedRow.nodes)
  have bodyEq : selected.packet.header.function.body = acceptedRow.statements := by
    have roots : selected.packet.header.function.source.roots = acceptedRow.statements.map NodeId.statement := by
      rw [selected.source_eq]
      exact acceptedRow.roots
    exact statement_roots (selected.packet.header.agreement.roots.symm.trans roots)
  have indexStatements : (index prepared selected.packet.aligned).statements = acceptedRow.statements := by
    have same : selected.packet.header.function.body = prepared.compilation.statements := by
      rw [selected.packet.aligned.function]
      rfl
    exact same.symm.trans bodyEq
  have indexShape : Shape (index prepared selected.packet.aligned).compilerSource
      selected.packet.header.function.resultType
      (Subset fixture.original.recipe.compiled.indexed acceptedRow.named row.original.function.typedBody) true
      (index prepared selected.packet.aligned).statements := by
    rw [indexStatements, selected.result_eq]
    show Shape (CallableIndexedNamedGeneration.source prepared.named) _ _ _ _
    rw [sourceSame]
    exact acceptedRow.shape
  have headerShape : Shape selected.packet.header.function.source selected.packet.header.function.resultType
      (Subset fixture.original.recipe.compiled.indexed acceptedRow.named selected.packet.header.function.source) true
      selected.packet.header.function.body := by
    rw [bodyEq, selected.result_eq, selected.source_eq]
    exact acceptedRow.shape
  obtain ⟨body, ready⟩ := CellAwarePublicAcceptedNamedRoot.refined_body prepared selected.packet.aligned
  obtain ⟨sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.original.checked fixture.original.accepted fixture.original.selected
  obtain ⟨allocated, sourceTrace⟩ := selected.tick_source_body actualShape ⟨[]⟩ flag
  obtain ⟨_stagedSize, trace⟩ := CellAwareInvocationAcceptedStatementLifting.body
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).evidence bodySelected)
    (support.certified selected.packet.header).runtime.graph.nodeOccurrencesUnique headerShape sourceTrace
  have covered := CellAwareInvocationAcceptedBodyShape.covered (index prepared selected.packet.aligned) rfl body.tree
    (semantic := (index prepared selected.packet.aligned).source)
    (expected := selected.packet.header.function.resultType)
    (admitted := CellAwareInvocationAcceptedMatches.Admitted (index prepared selected.packet.aligned))
    (generalized := CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True)
      (index prepared selected.packet.aligned))
    ready indexShape
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedNamedForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
  refine ⟨⟨start, ⟨requiredExecution, requiredOutput, ?_⟩, ⟨value, finalStore, required, run⟩, ?_⟩⟩
  · intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨returned, actual, generation, _reached, same, succeeded, indexed, _⟩ :=
      output executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    exact ⟨returned, actual, generation, _, _, same, succeeded, indexed⟩
  · intro fuel completedValue completedStore completed
    obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
        bound', staged, result, _named⟩ :=
      CellAwarePublicAcceptedNamedRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
        selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
        initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
        initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
        initial.heaps rfl start.started completed
    exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, bound', staged, result⟩

namespace AcceptedTickRuntime

/-- Each call starts a fresh actual session. The plan is kernel-checked against
whatever the observed compile, check and start receipts are; the resume runs the
real compiled code. -/
def run : IO Unit := do
  let observed ← observe
  let acceptedRow ← observeAcceptedRow observed.fixture observed.tick
  for flag in [true, false] do
    let started ← observeStarted observed.fixture.original observed.tick.original.key [.bool flag]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.tick),
        Nonempty (AcceptedTick selected flag started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.typing.wellFormed
      obtain ⟨selected⟩ := whole.select observed.tick
      exact ⟨whole, selected, accepted_tick selected observed.tickShape acceptedRow flag observed.typing.wellFormed
        started observed.callableProfile⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .bool flag do throw (IO.userError "accepted tick output changed")
    | _ => throw (IO.userError "accepted tick call did not succeed")
  IO.println "ACCEPTED_TICK_PUBLIC_PASS"

end AcceptedTickRuntime

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportCollected
/-! Actual observed factory output retains every selected leaf together with
its independent Source value and exact returned physical session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem selected_original {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicOutputSelections.Selected (same ▸ selection) source native type fuel entries) :
    RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries := by
  cases same
  exact selected

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape flag started callableProfile) :=
  CellAwareSelectedPublicSessionState.functions whole.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape flag started callableProfile) :=
  CellAwareSelectedPublicSessionState.cells whole.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape flag started callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List Entry) where
  state : CellAwarePublicSessionState.State whole.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

/-- A successful observed factory result is linked to its Source-produced
closures without a numeric sufficient-fuel premise. -/
theorem InitialForward.observed_collected
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (retained : first.Retained returned.session entries) (payload : Core.Value),
      entries.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries ∧
      retained.state.heap = (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body (selected.make_shape shape) typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.first_collected _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,entries,_native,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries := selected_original atReturned.1 selectedLeaves
    refine ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)),
      store := store, caller := reached, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩,payload,?_,selectedPublic,rfl⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportContinuation
/-! Later factory and ordinary calls use the returned physical session. Their
complete Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {firstRow : Row fixture.original}
  {selected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {started : Started fixture.original firstRow.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected firstShape firstFlag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  {row : Row fixture.original} (next : SelectedInventory whole row)

structure NextSourcePlan (publicArguments : List SourceCorePublicValues.Value) (arguments : List Dynamic.Value)
    (call : StartedCall session row.original.key publicArguments runOptions)
    (value : Dynamic.Value) (after : Dynamic.Heap) where
  start : CellAwarePublicNextStart.Started (header := next.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start arguments
  environment : Dynamic.Environment
  bound : Dynamic.Heap
  finalContext : SourceSemantics.Context
  allocated : Dynamic.BindersAllocate [] retained.state.heap next.packet.header.function.parameters arguments environment bound
  sourceTrace : Dynamic.FunctionStatementsExecute
    (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    next.packet.header.context next.packet.header.function.evidence next.packet.header.function.source
    environment bound next.packet.header.function.body finalContext (.returned value) after

private theorem selected_start
    {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session row.original.key publicArguments runOptions) :
    Nonempty (CellAwarePublicNextStart.Started (header := next.packet.header) retained.state call) := by
  apply CellAwarePublicNextStart.from_call (prepared := fixture.ready) retained.state call
  intro root found
  apply next.root_selection (List.mem_of_find?_eq_some found)
  exact of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root fixture.original.recipe.compiled =>
      decide (candidate.key = row.original.key)) found)

/-- Capture retains the earlier history and constructs its own authentic
parameter allocation and generalized closure return at that exact heap. -/
theorem capture_plan
    (shape : CaptureShape row.original.function.typedBody) (seed : Word)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.word seed] runOptions) :
    Nonempty (NextSourcePlan first retained next [.word seed] [.word seed] call
      ((next.capture_shape shape).value next.packet.header.context
        (snapshotEnvironment (next.capture_shape shape).principal.input retained.state.heap .word (.word seed))
        next.packet.header.function.evidence)
      ((next.capture_shape shape).principal.allocatedHeap next.packet.header.context
        (snapshotEnvironment (next.capture_shape shape).principal.input retained.state.heap .word (.word seed))
        (snapshotHeap retained.state.heap .word (.word seed)))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.capture_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.word seed] next.packet.header.types := by
    rw [next.capture_input_types actualShape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  obtain ⟨allocated,final,trace⟩ := next.capture_source_body actualShape typing.wellFormed retained.state.heap seed
  exact ⟨⟨start,ready,_,_,final,allocated,trace⟩⟩

/-- An unrelated ordinary row uses the same complete inventory and returned
state, with a genuine Source parameter allocation and read. -/
theorem tick_plan
    (shape : TickShape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextSourcePlan first retained next [.bool flag] [.bool flag] call
      (.bool flag) (inputHeap retained.state.heap .bool (.bool flag))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.tick_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.bool flag] next.packet.header.types := by
    rw [next.tick_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  obtain ⟨allocated,trace⟩ := next.tick_source_body actualShape retained.state.heap flag
  exact ⟨⟨start,ready,_,_,_,allocated,trace⟩⟩

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/
theorem NextSourcePlan.observed_collected
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨stagedContext,stagedOutcome,heap,capture,native,store,mapping,world,required,adapted,run,result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,_native,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportMaterialized
/-! Actual factory output carries positive generalized materialization through
Source lifting, public encoding and exact selected exported leaves. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- A successful observed factory result is linked to its Source-produced
closures without a numeric sufficient-fuel premise. -/
theorem InitialForward.observed_materialized
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (retained : first.Retained returned.session entries) (payload : Core.Value),
      entries.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries ∧
      retained.state.heap = (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)) ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled retained.state.mapping retained.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation entries := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  let profile := materialized.for_selected selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body (selected.make_shape shape) typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.first_collected _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,entries,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)),
      store := store, caller := reached, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩,payload,?_,selectedPublic,rfl,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

section Continuation
open SelectedCompilationPublicSessionState (StartedCall)
variable {firstRow : Row fixture.original}
  {firstSelected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original firstRow.original.key [.bool firstFlag]}
  (first : InitialForward firstSelected firstShape firstFlag firstStart callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (next : SelectedInventory whole row)

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/
theorem NextSourcePlan.observed_materialized
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (typing : OriginalTyping fixture.original)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled continued.state.mapping continued.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation added := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  let profile := materialized.for_selected next
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨capture,stagedContext,stagedOutcome,heap,native,store,mapping,world,required,adapted,run,result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header firstSelected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Continuation

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportSelection
/-! Finite output selections expose the actual Source/native leaves of the
original pair and single factory returns. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

def pairSelection {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right)) : Selection type value := by
  cases types
  cases values
  exact .product .function .function

theorem pairSelection_handles {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right)) :
    (pairSelection types values).handles = [left,right] := by
  cases types
  cases values
  rfl

theorem pair_selected {type leftType rightType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {left right : SourceCorePublicValues.Handle}
    (types : type = .product leftType rightType)
    (values : value = .product (.function left) (.function right))
    {first second : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (pairSelection types values) (.product first second) native nativeType fuel entries) :
    ∃ firstNative secondNative firstType secondType remaining,
      entries = [⟨leftType,first,left,firstNative,firstType,remaining⟩,
        ⟨rightType,second,right,secondNative,secondType,remaining⟩] := by
  cases types
  cases values
  cases selected with
  | product leftSelected rightSelected =>
    cases leftSelected
    cases rightSelected
    exact ⟨_,_,_,_,_,rfl⟩

def functionSelection {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle) : Selection type value := by
  cases same
  exact .function

theorem function_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (functionSelection (type := type) same) source native nativeType fuel entries) :
    entries = [⟨type,source,handle,native,nativeType,fuel⟩] := by
  cases same
  cases selected
  rfl

theorem skip_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (Selection.skip (type := type) (value := value)) source native nativeType fuel entries) :
    entries = [] := by
  cases selected
  rfl

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedIdentitySource
/-! Independent Source execution for a generalized identity lambda. The shape
retains only its actual binder, parameter and original body occurrences. Each
instance call copies the descriptor's captures before allocating its
parameter, as closures capture by value. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedIdentity
open Solcore Frontend SourceInference SourceSemantics

structure IdentityShape (source : TypedSource) where
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  lambda : ExpressionNode
  identityReturn : StatementNode
  parameterRead : Tests.SourceCoreNamedBranch.Read source parameter (.variable typeVariable)
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  identityFound : source.lookupStatement? identityReturn.id = some identityReturn
  identityForm : identityReturn.form = .returnStmt (some parameterRead.node.id)

def IdentityShape.descriptor {source : TypedSource} (shape : IdentityShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (.variable shape.typeVariable) [shape.identityReturn.id]

theorem IdentityShape.captures {source : TypedSource} (shape : IdentityShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

/-- The exact materialized body copies the descriptor's captures, reads its
newly allocated parameter and returns it. The supplied frame is static Source
code/evidence validity. -/
theorem IdentityShape.identity_applies {source : TypedSource} (shape : IdentityShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument)
      ⟨copied.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.parameterRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.parameterRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.parameterRead.form, shape.parameterRead.requirements, shape.parameterRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.parameterRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.identityReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.identityFound))
      (by simp only [StatementNode.applySubstitution, shape.identityForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)) copy
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.identityFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.identityForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl

/-- A read selects the actual instance before the ordered argument evaluation.
The call copies the captures and allocates the identity parameter only after
that argument finishes. -/
theorem IdentityShape.invoke {source : TypedSource} (shape : IdentityShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : Tests.SourceCoreSelectedInterleavedLocal.CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured argumentsHeap entry copied) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      argument ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  have callee : Dynamic.ExpressionEvaluates program context evidence source environment before
      call.callee.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) before := by
    apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
      (lookupExpression?_sound call.callee.found) call.callee.form
      (by rw [call.callee.requirements, call.callee.coercions]; rfl)
      lookup read descriptor fields
    · rw [call.callee.raw]; exact instantiation
    · rw [call.callee.coercions]; exact .nil
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      (shape.identity_applies captured substitution _ evidence argumentsHeap argument copy frame)
  · rw [call.coercions]; exact .nil

/-- The two runtime instances use an exact singleton substitution. Original
scheme validity and the requested ground type are the only typing inputs. -/
theorem IdentityShape.instance {source : TypedSource} (shape : IdentityShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil

/-- Deep typing of the actual captured descriptor supplies the static invocation
frame for each instance, independently of executing either call. -/
theorem IdentityShape.frame {source : TypedSource} (shape : IdentityShape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (evidence : Dynamic.EvidenceEnvironment) {type : TypeSystem.Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.GeneralizedClosureWellTyped nextContext heap (shape.descriptor context environment))
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (signatures : nextContext.signatures = program.signatures)
    (covers : evidence.Covers nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (ground : TypeWellFormed nextContext type) :
    Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, type)]
        (evidence.applySubstitution [(shape.typeVariable, type)])) := by
  have materialized := Dynamic.GeneralizedClosureWellTyped.instantiateHasType
    catalog typed fields covers (shape.instance evidence wellformed ground)
  obtain ⟨_parameter, _result, same, code, closed, _captured⟩ := materialized.closure_function_inv
  exact ⟨same.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, closed⟩

private theorem descriptor_scheme_of_typed
    {source : TypedSource} {context : SourceSemantics.Context}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType source context node.id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    SchemeWellFormed context function.binder.scheme := by
  generalize outputEq : node.type = output at typed
  cases typed with
  | intro contains formTyped rawType _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at formTyped
    cases formTyped with
    | reference reference =>
      cases reference with
      | «local» schemeLookup _ valid =>
        have identity := locals.lookup_generalized schemeLookup lookup read descriptor
        cases valid with
        | intro _ formed _ _ _ _ _ _ _ => exact identity.2 ▸ formed

/-- The actual typed lexical occurrence and deeply typed stored descriptor
supply scheme validity and the invocation frame before the supplied argument
runs. Ground argument types are static Source typing facts. The call copies the
descriptor's captures from the heap the argument leaves. -/
theorem IdentityShape.invoke_from_typed {source : TypedSource} (shape : IdentityShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : Tests.SourceCoreSelectedInterleavedLocal.CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (evidence : Dynamic.EvidenceEnvironment)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context call.callee.node.id call.callee.node.type)
    (ground : TypeWellFormed context type)
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution [(shape.typeVariable, type)]) captured
      argumentsHeap entry copied) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      argument ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution
        [(shape.typeVariable, type)]).scheme.body, value := some argument}]⟩ := by
  have wellformed := descriptor_scheme_of_typed runtime.graph.nodeOccurrencesUnique
    call.callee.found call.callee.form typed locals lookup read descriptor
  have descriptorTyped := ((heapTyped cell read.member).generalized_inv descriptor).2
  have frame := shape.frame captured before evidence
    (by simpa only [fields.signatures] using catalog) descriptorTyped fields
    runtime.signatures covers wellformed ground
  exact shape.invoke call captured environment [(shape.typeVariable, type)] evidence []
    lookup read descriptor fields (shape.instance evidence wellformed ground) frame argumentTrace copy

end Tests.SourceCoreGeneralizedIdentity
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedSelectedRegistry
/-! The original declarative rows authenticate only the selected cache origins.
Actual cached replacement observations supply the unchanged registry ranges. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

theorem OriginalTyping.selected_bodies {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    SelectedCompilationBodyTyping.Bodies fixture.recipe.compiled := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.checked
  obtain ⟨functionIds,methodIds⟩ := Frontend.checkProgram_success_ids fixture.checked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,FunctionDefinition.ofChecked,BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro function selected
    obtain ⟨_,_,_,_,_,_,member,_⟩ := selected
    apply functionDefinitionValid_ofCheckProgram fixture.checked member
    intro signature signatureMember accepted
    obtain ⟨typed⟩ := original.functions.at member
    have same : signature = typed.signature := by
      apply eq_of_mem_of_nodup_map catalog.function_ids signatureMember typed.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans typed.owner
    subst signature
    apply checkedBodyHasType_ofStatements accepted
    exact typed.body.statements_typed
  · intro method selected
    obtain ⟨_,_,_,_,_,_,member,_,_⟩ := selected
    rw [original.methods] at member
    cases member

theorem ObservedCache.ranges {fixture : CompiledFixture}
    (cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions) :
    SelectedCompilationRegistryMethodCertificates.Ranges fixture.recipe.compiled := by
  intro index named selected
  obtain ⟨observation⟩ := cache.at_slot selected
  rw [observation.substitution]
  intro name value found
  cases found

theorem OriginalTyping.checked_registry {fixture : CompiledFixture} (original : OriginalTyping fixture)
    (cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions) :
    SelectedCompilationCheckedRegistry.Certificate fixture.recipe.compiled :=
  SelectedCompilationCheckedRegistry.of_checked fixture.checked original.selected_bodies cache.ranges

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportHandlePlan
/-! A retained exact Source closure supplies its ordinary application before
resuming its actual packed public handle call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected shape flag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (entry : Entry) {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
  (call : CellAwarePublicHandleStart.StartedCall session entry.handle argument runOptions.inputValidationFuel)

structure HandleSourcePlan (parameter result : TypeSystem.Ty) (sourceArgument value : Dynamic.Value) (after : Dynamic.Heap) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter result
  start : CellAwarePublicHandleStart.Started retained.state entry call parameter result
  ready : CellAwarePublicHandleStart.Ready retained.state entry call start sourceArgument
  function : Dynamic.Closure
  sourceEq : entry.source = .closure function
  materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
    retained.state.mapping retained.state.world entry
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument
  callerEvidence : Dynamic.EvidenceEnvironment
  invocationEvidence : Dynamic.EvidenceEnvironment
  arity : [sourceArgument].length = function.parameters.length
  trace : Dynamic.CallableApplies (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.function.context callerEvidence invocationEvidence retained.state.heap
    entry.source [sourceArgument] value after

/-- A retained closure's captured cells agree with the current heap, so its
call can copy them. -/
theorem retained_copies (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    {function : Dynamic.Closure} (sourceEq : entry.source = .closure function) :
    ∃ environment copied, Dynamic.EnvironmentCopies function.source function.captured
      retained.state.heap environment copied := by
  obtain ⟨_imported, _represented, typed⟩ := retained.state.history.semantic.current.2.2.2.2 entry member
  rw [entryType, sourceEq] at typed
  exact CellAwareGeneralizedSourceInversion.copies_exist function.source typed.closure_function_inv.2.2.2.2.2

/-- A genuine identity instance copies its captured cells, returns the actual
input and appends exactly its parameter cell. Its Source frame comes from the
retained typed history. -/
theorem identity_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    (materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entry)
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument)
    {source : TypedSource} (identity : MakeShape source)
    (definitionContext : SourceSemantics.Context) (captured : Dynamic.Environment)
    (substitution : TypeSystem.Substitution) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEq : entry.source = .closure ((identity.principal.descriptor definitionContext captured).instantiate substitution evidence))
    (typing : OriginalTyping fixture.original) :
    ∃ (environment : Dynamic.Environment) (copied : Dynamic.Heap),
      Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured retained.state.heap environment copied ∧
      Nonempty (HandleSourcePlan first retained entry call parameter result sourceArgument sourceArgument
        ⟨copied.cells ++ [{type := (identity.principal.parameter.applySubstitution substitution).scheme.body, value := some sourceArgument}]⟩) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  have frame := CellAwarePublicRetainedMaterializedHandle.source_frame first.functions
    typing.selected_bodies ready.history.semantic entry member entryType sourceEq
  obtain ⟨environment, copied, copy⟩ := retained_copies first retained entry member entryType sourceEq
  have trace := identity.identity_applies (context := selected.packet.header.function.context)
    captured substitution evidence [] retained.state.heap sourceArgument copy frame
  exact ⟨environment, copied, copy, ⟨⟨member,entryType,start,ready,_,sourceEq,materialized,input,[],evidence,rfl,sourceEq.symm ▸ trace⟩⟩⟩

/-- The captured instance copies its captured cells and reads the copy of the
saved cell, preserved in the current Source heap, before returning its
unchanged value. -/
theorem captured_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    (materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entry)
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument)
    {source : TypedSource} (capture : CaptureShape source)
    (definitionContext : SourceSemantics.Context) (captured : Dynamic.Environment)
    (substitution : TypeSystem.Substitution) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEq : entry.source = .closure ((capture.principal.descriptor definitionContext captured).instantiate substitution evidence))
    {location : Dynamic.Location} {cell : Dynamic.Cell} {saved : Dynamic.Value}
    (capturedLookup : Dynamic.Environment.LooksUp captured capture.principal.input.id location)
    (capturedRead : Dynamic.Heap.Reads retained.state.heap location cell)
    (ordinary : cell.generalized = none) (capturedValue : cell.value = some saved)
    (typing : OriginalTyping fixture.original) :
    ∃ (environment : Dynamic.Environment) (copied : Dynamic.Heap),
      Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured retained.state.heap environment copied ∧
      Nonempty (HandleSourcePlan first retained entry call parameter result sourceArgument saved
        ⟨copied.cells ++ [{type := (capture.principal.parameter.applySubstitution substitution).scheme.body, value := some sourceArgument}]⟩) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  have frame := CellAwarePublicRetainedMaterializedHandle.source_frame first.functions
    typing.selected_bodies ready.history.semantic entry member entryType sourceEq
  obtain ⟨environment, copied, copy⟩ := retained_copies first retained entry member entryType sourceEq
  have trace := capture.captured_applies (context := selected.packet.header.function.context)
    captured substitution evidence [] retained.state.heap sourceArgument saved copy capturedLookup capturedRead
    ordinary capturedValue frame
  exact ⟨environment, copied, copy, ⟨⟨member,entryType,start,ready,_,sourceEq,materialized,input,[],evidence,rfl,sourceEq.symm ▸ trace⟩⟩⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportHandleObserved
/-! The observed result of the already planned independent Source call retains
all exported functions at its exact returned Source/native heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {first : InitialForward selected shape flag started callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {retained : first.Retained session entries}
  {entry : Entry} {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
  {call : CellAwarePublicHandleStart.StartedCall session entry.handle argument runOptions.inputValidationFuel}

/-- No result of the current target is used to construct the independent call.
Its actual completion identifies the same final store by native determinism. -/
theorem HandleSourcePlan.observed_retained {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : HandleSourcePlan first retained entry call parameter result sourceArgument value after)
    (typing : OriginalTyping fixture.original)
    (origins : CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entries)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    ∃ continued : first.Retained returned.session entries,
      continued.state.heap = after ∧
      CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
        continued.state.mapping continued.state.world entries := by
  obtain ⟨sidecar,_issued,_selected⟩ := selected.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size (.value plan.trace)
  have metadata : SourceCoreRawMetadata.Extends plan.start.encodedValues.registry
      plan.ready.receiving.result.context.registry := by
    rw [plan.ready.contextAt]
    exact .refl _
  obtain ⟨native,store,mapping,world,required,run,resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.source_has_sufficient_fuel
      (invocation := RecursiveStageRegistry.scope sidecar [] selected.packet.header.function)
      first.functions callableProfile plan.ready.issued plan.ready.receiving.result.extension
      (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) typing.wellFormed
      plan.ready.history.semantic entry plan.member plan.entryType plan.sourceEq plan.materialized plan.input
      plan.start.started plan.start.parameterView metadata (.singleton sourceArgument) plan.arity measured
  obtain ⟨actual,generation,reached,_exported,atReturned,_related,history,registry,exportsReady⟩ :=
    CellAwarePublicDirectObservedOutput.after_success _ _ plan.start.started
      (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt) retained.exportsReady
      plan.start.atCheckpoint resultAt (run required (Nat.le_refl _)) resumed plan.ready.history
  exact ⟨⟨{
    artifact := retained.state.artifact, session := actual.session,
    mapping := mapping, world := world, heap := after, store := store, caller := reached,
    atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
    receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
    registry := registry, history := history
    },exportsReady⟩,rfl,origins.extend resultAt.2.2.1 resultAt.2.2.2.1⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedNamedSelectedInventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories
theorem ProfiledFixture.inventory_selected (fixture : ProfiledFixture)
    (cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled) :
    Nonempty (WholeInventory fixture) := by
  classical
  let functions := fixture.original.recipe.compiled.indexed.base.functions
  have available : ∀ position : Fin functions.length, ∃ input : Input fixture.original.recipe.compiled,
      input.prepared.index = position.val ∧ input.prepared.named = functions[position.val] := by
    intro position
    have selected : functions[position.val]? = some functions[position.val] := List.getElem?_eq_getElem position.isLt
    obtain ⟨observation⟩ := cache.at_slot selected
    have origin := SelectedCompilationCatalog.ordinary_origin fixture.original.recipe.compiled
      bodies.signatures (RecursiveNamedPreparedFinalPlanOrigins.final_member _ selected rfl)
      observation.member observation.declaration
    have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
        functions[position.val].specialized.parameterSubstitution := by
      rw [observation.substitution]
      intro name value found
      cases found
    obtain ⟨input, _row, slot, named⟩ := SelectedCompilationCatalog.of_cached fixture.original.recipe.compiled
      bodies.signatures selected origin range observation.ordinary observation.parameters
    exact ⟨input, slot, named⟩
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := (List.finRange functions.length).map choose
  obtain ⟨rows⟩ := SelectedCompilationCatalog.inventory bodies inputs
  refine ⟨⟨inputs, rows, ?_⟩⟩
  simp only [inputs, List.map_map]
  exact List.map_congr_left (fun position _ => (chosen position).1)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.make_source_body_selected (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .bool (.bool flag)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .bool (.bool flag)) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .bool (.bool flag)) (snapshotHeap before .bool (.bool flag))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (inputHeap before .bool (.bool flag)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    SelectedCompilationHeaderCertificates.certified bodies header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.make_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag))
    (shape.principal.input_snapshot before _ _)
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.make_statements shape ▸ body⟩

theorem SelectedInventory.capture_source_body_selected (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled)
    (before : Dynamic.Heap) (seed : Word) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .word (.word seed)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .word (.word seed)) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment shape.principal.input before .word (.word seed)) (snapshotHeap before .word (.word seed))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .word (some (.word seed))
      ⟨before.cells.length⟩ (inputHeap before .word (.word seed)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    SelectedCompilationHeaderCertificates.certified bodies header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.capture_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed))
    (shape.principal.input_snapshot before _ _)
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.capture_statements shape ▸ body⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedNamedSelectedPublic
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem initial_from_source_selected (selected : SelectedInventory whole row)
    (shape : MakeShape row.original.function.typedBody) (flag : Bool)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  let actualShape := selected.make_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.make_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body_selected actualShape support.bodyTyping ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value_selected callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic support
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩
end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedNamedSelectedContinuation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {firstRow : Row fixture.original}
  {selected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {started : Started fixture.original firstRow.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected firstShape firstFlag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  {row : Row fixture.original} (next : SelectedInventory whole row)

/-- Capture retains the earlier history and constructs its own authentic
parameter allocation and generalized closure return at that exact heap. -/
theorem capture_plan_selected
    (shape : CaptureShape row.original.function.typedBody) (seed : Word)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (call : StartedCall session row.original.key [.word seed] runOptions) :
    Nonempty (NextSourcePlan first retained next [.word seed] [.word seed] call
      ((next.capture_shape shape).value next.packet.header.context
        (snapshotEnvironment (next.capture_shape shape).principal.input retained.state.heap .word (.word seed))
        next.packet.header.function.evidence)
      ((next.capture_shape shape).principal.allocatedHeap next.packet.header.context
        (snapshotEnvironment (next.capture_shape shape).principal.input retained.state.heap .word (.word seed))
        (snapshotHeap retained.state.heap .word (.word seed)))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.capture_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.word seed] next.packet.header.types := by
    rw [next.capture_input_types actualShape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    support.bodyTyping start inputTypes inputMeanings
  obtain ⟨allocated,final,trace⟩ := next.capture_source_body_selected actualShape support.bodyTyping retained.state.heap seed
  exact ⟨⟨start,ready,_,_,final,allocated,trace⟩⟩

/-- An unrelated ordinary row uses the same complete inventory and returned
state, with a genuine Source parameter allocation and read. -/

theorem tick_plan_selected
    (shape : TickShape row.original.function.typedBody) (flag : Bool)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextSourcePlan first retained next [.bool flag] [.bool flag] call
      (.bool flag) (inputHeap retained.state.heap .bool (.bool flag))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.tick_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.bool flag] next.packet.header.types := by
    rw [next.tick_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    support.bodyTyping start inputTypes inputMeanings
  obtain ⟨allocated,trace⟩ := next.tick_source_body actualShape retained.state.heap flag
  exact ⟨⟨start,ready,_,_,_,allocated,trace⟩⟩

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/

theorem NextSourcePlan.observed_collected_selected
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨stagedContext,stagedOutcome,heap,capture,native,store,mapping,world,required,adapted,run,result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel_selected callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic support
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header selected.packet.header
        support.bodyTyping).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,_native,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded
end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedNamedSelectedMaterialized
/-! Actual factory output carries positive generalized materialization through
Source lifting, public encoding and exact selected exported leaves. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- A successful observed factory result is linked to its Source-produced
closures without a numeric sufficient-fuel premise. -/
theorem InitialForward.observed_materialized_selected
    (first : InitialForward selected shape flag started callableProfile)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (retained : first.Retained returned.session entries) (payload : Core.Value),
      entries.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries ∧
      retained.state.heap = (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)) ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled retained.state.mapping retained.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation entries := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  let profile := materialized.for_selected selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body_selected (selected.make_shape shape) support.bodyTyping ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel_selected callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic support
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        support.bodyTyping).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.first_collected _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,entries,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (snapshotEnvironment (selected.make_shape shape).principal.input ⟨[]⟩ .bool (.bool flag)) (snapshotHeap ⟨[]⟩ .bool (.bool flag)),
      store := store, caller := reached, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩,payload,?_,selectedPublic,rfl,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

section Continuation
open SelectedCompilationPublicSessionState (StartedCall)
variable {firstRow : Row fixture.original}
  {firstSelected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original firstRow.original.key [.bool firstFlag]}
  (first : InitialForward firstSelected firstShape firstFlag firstStart callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (next : SelectedInventory whole row)

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/
theorem NextSourcePlan.observed_materialized_selected
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled continued.state.mapping continued.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation added := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  let profile := materialized.for_selected next
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨capture,stagedContext,stagedOutcome,heap,native,store,mapping,world,required,adapted,run,result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel_selected callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic support
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header firstSelected.packet.header
        support.bodyTyping).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Continuation

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportHistory
/-! Concrete exported entries retain their exact independent Source closures.
The complete original inventory and positive materialized history stay attached. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

structure IdentityEntry (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (parameter result : TypeSystem.Ty) where
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function parameter result
  source : TypedSource
  shape : MakeShape source
  definitionContext : SourceSemantics.Context
  captured : Dynamic.Environment
  substitution : TypeSystem.Substitution
  evidence : Dynamic.EvidenceEnvironment
  sourceEq : entry.source = .closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)

def IdentityEntry.append {entries : List Entry} {handle : SourceCorePublicValues.Handle}
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry entries handle parameter result) (added : List Entry) :
    IdentityEntry (entries ++ added) handle parameter result :=
  { identity with member := List.mem_append_left added identity.member }

structure CaptureEntry (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (heap : Dynamic.Heap) (seed : Word) where
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function .bool .word
  source : TypedSource
  shape : CaptureShape source
  definitionContext : SourceSemantics.Context
  captured : Dynamic.Environment
  substitution : TypeSystem.Substitution
  evidence : Dynamic.EvidenceEnvironment
  sourceEq : entry.source = .closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)
  location : Dynamic.Location
  lookup : Dynamic.Environment.LooksUp captured shape.principal.input.id location
  read : Dynamic.Heap.Reads heap location {type := .word, value := some (.word seed)}

structure Context (observed : Observed) where
  whole : WholeInventory observed.fixture
  selected : SelectedInventory whole observed.make
  start : Started observed.fixture.original observed.make.original.key [.bool true]
  first : InitialForward selected observed.makeShape true start observed.callableProfile

variable {observed : Observed} (context : Context observed)
  {artifact : SourceCoreExecution.Artifact}

structure PairHistory (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle : SourceCorePublicValues.Handle) where
  entries : List Entry
  retained : context.first.Retained session entries
  origins : CellAwareMaterializedRetainedEntries.Retained (keys observed.fixture.original.recipe.compiled)
    retained.state.mapping retained.state.world entries
  wordEntry : IdentityEntry entries wordHandle .word .word
  boolEntry : IdentityEntry entries boolHandle .bool .bool

structure FullHistory (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) where
  pair : PairHistory context session wordHandle boolHandle
  captured : CaptureEntry pair.entries captureHandle pair.retained.state.heap seed

/-- Exact selected Source leaves create the two entries used by later calls. -/
theorem Context.collected {executionFuel outputFuel : Nat}
    {returned : SourceCoreExecution.Completion context.start.artifact}
    (resumed : context.start.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    {wordHandle boolHandle : SourceCorePublicValues.Handle}
    (valueEq : returned.value = .product (.function wordHandle) (.function boolHandle)) :
    Nonempty (PairHistory context returned.session wordHandle boolHandle) := by
  have typeEq := context.selected.result_eq.trans observed.makeResult
  let selection := pairSelection typeEq valueEq
  obtain ⟨entries,retained,payload,_handles,selectedLeaves,_heap,materialized⟩ :=
    context.first.observed_materialized_selected (observed.typing.checked_registry observed.cache).namedSupport observed.makeProfile resumed selection
  obtain ⟨firstNative,secondNative,firstType,secondType,remaining,entriesEq⟩ :=
    pair_selected typeEq valueEq selectedLeaves
  subst entries
  let shape := context.selected.make_shape observed.makeShape
  let captured := snapshotEnvironment shape.principal.input ⟨[]⟩ .bool (.bool true)
  refine ⟨⟨_,retained,CellAwareMaterializedRetainedEntries.Retained.of_selected
    (owner observed.fixture.original.recipe.compiled) materialized,?_,?_⟩⟩
  · exact ⟨⟨.function .word .word,
      .closure ((shape.principal.descriptor context.selected.packet.header.context captured).instantiate
        [(shape.principal.typeVariable,.word)]
        (context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.word)])),
      wordHandle,firstNative,firstType,remaining⟩,List.mem_cons_self,rfl,rfl,_,shape,context.selected.packet.header.context,captured,
      [(shape.principal.typeVariable,.word)],
      context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.word)],rfl⟩
  · exact ⟨⟨.function .bool .bool,
      .closure ((shape.principal.descriptor context.selected.packet.header.context captured).instantiate
        [(shape.principal.typeVariable,.bool)]
        (context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)])),
      boolHandle,secondNative,secondType,remaining⟩,List.mem_cons_of_mem _ (List.mem_cons_self),rfl,rfl,_,shape,context.selected.packet.header.context,captured,
      [(shape.principal.typeVariable,.bool)],
      context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)],rfl⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportNamedSteps
/-! Factory and unrelated named calls preserve the earlier exported instances
and the exact saved Source cell across their real public completions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (StartedCall)

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

structure CapturePlan (history : PairHistory context session wordHandle boolHandle) (seed : Word)
    (call : StartedCall session observed.capture.original.key [.word seed] runOptions) where
  selected : SelectedInventory context.whole observed.capture
  plan : NextSourcePlan context.first history.retained selected [.word seed] [.word seed] call
    ((selected.capture_shape observed.captureShape).value selected.packet.header.context
      (snapshotEnvironment (selected.capture_shape observed.captureShape).principal.input history.retained.state.heap .word (.word seed))
      selected.packet.header.function.evidence)
    ((selected.capture_shape observed.captureShape).principal.allocatedHeap selected.packet.header.context
      (snapshotEnvironment (selected.capture_shape observed.captureShape).principal.input history.retained.state.heap .word (.word seed))
      (snapshotHeap history.retained.state.heap .word (.word seed)))

theorem PairHistory.plan_capture (history : PairHistory context session wordHandle boolHandle) (seed : Word)
    (call : StartedCall session observed.capture.original.key [.word seed] runOptions) :
    Nonempty (CapturePlan history seed call) := by
  obtain ⟨selected⟩ := context.whole.select observed.capture
  obtain ⟨plan⟩ := capture_plan_selected context.first history.retained selected observed.captureShape seed (observed.typing.checked_registry observed.cache).namedSupport call
  exact ⟨⟨selected,plan⟩⟩

theorem CapturePlan.collected {history : PairHistory context session wordHandle boolHandle}
    {call : StartedCall session observed.capture.original.key [.word seed] runOptions}
    (planned : CapturePlan history seed call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (valueEq : returned.value = .function captureHandle) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  let selected := planned.selected
  let shape := selected.capture_shape observed.captureShape
  let environment := snapshotEnvironment shape.principal.input history.retained.state.heap .word (.word seed)
  let selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value :=
    functionSelection valueEq
  obtain ⟨added,continued,payload,_handles,selectedLeaf,heapEq,maps,worlds,materialized⟩ :=
    planned.plan.observed_materialized_selected context.first history.retained selected (observed.typing.checked_registry observed.cache).namedSupport
      observed.captureProfile resumed selection
  have addedEq := function_selected valueEq selectedLeaf
  subst added
  let entry : Entry := ⟨selected.packet.header.function.resultType,
    shape.value selected.packet.header.context environment selected.packet.header.function.evidence,
    captureHandle,payload,selected.packet.header.output,outputFuel⟩
  have copied : Dynamic.Heap.Allocates (inputHeap history.retained.state.heap .word (.word seed)) .word
      (some (.word seed)) ⟨(inputHeap history.retained.state.heap .word (.word seed)).cells.length⟩
      (snapshotHeap history.retained.state.heap .word (.word seed)) := .append
  have generalized : Dynamic.Heap.AllocatesGeneralized (snapshotHeap history.retained.state.heap .word (.word seed))
      (shape.principal.descriptor selected.packet.header.context environment)
      ⟨(snapshotHeap history.retained.state.heap .word (.word seed)).cells.length⟩
      (shape.principal.allocatedHeap selected.packet.header.context environment
        (snapshotHeap history.retained.state.heap .word (.word seed))) := .append
  have read := generalized.preserves_read copied.reads_new
  refine ⟨⟨⟨_,continued,(history.origins.extend maps worlds).append
    (CellAwareMaterializedRetainedEntries.Retained.of_selected (owner observed.fixture.original.recipe.compiled) materialized),
    history.wordEntry.append [entry],history.boolEntry.append [entry]⟩,?_⟩⟩
  exact ⟨entry,List.mem_append_right _ List.mem_cons_self,rfl,selected.result_eq.trans observed.captureResult,
    _,shape,selected.packet.header.context,environment,[(shape.principal.typeVariable,.bool)],
    selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)],rfl,
    ⟨(inputHeap history.retained.state.heap .word (.word seed)).cells.length⟩,.head,heapEq.symm ▸ read⟩

structure TickPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed) (flag : Bool)
    (call : StartedCall session observed.tick.original.key [.bool flag] runOptions) where
  selected : SelectedInventory context.whole observed.tick
  plan : NextSourcePlan context.first history.pair.retained selected [.bool flag] [.bool flag] call
    (.bool flag) (inputHeap history.pair.retained.state.heap .bool (.bool flag))

theorem FullHistory.plan_tick (history : FullHistory context session wordHandle boolHandle captureHandle seed) (flag : Bool)
    (call : StartedCall session observed.tick.original.key [.bool flag] runOptions) :
    Nonempty (TickPlan history flag call) := by
  obtain ⟨selected⟩ := context.whole.select observed.tick
  obtain ⟨plan⟩ := tick_plan_selected context.first history.pair.retained selected observed.tickShape flag (observed.typing.checked_registry observed.cache).namedSupport call
  exact ⟨⟨selected,plan⟩⟩

theorem TickPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {flag : Bool} {call : StartedCall session observed.tick.original.key [.bool flag] runOptions}
    (planned : TickPlan history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨added,continued,payload,_handles,selectedLeaf,heapEq,maps,worlds⟩ :=
    planned.plan.observed_collected_selected context.first history.pair.retained planned.selected (observed.typing.checked_registry observed.cache).namedSupport resumed .skip
  have addedEq := skip_selected selectedLeaf
  subst added
  have allocated : Dynamic.Heap.Allocates history.pair.retained.state.heap .bool (some (.bool flag))
      ⟨history.pair.retained.state.heap.cells.length⟩ (inputHeap history.pair.retained.state.heap .bool (.bool flag)) := .append
  refine ⟨⟨⟨_,continued,(history.pair.origins.extend maps worlds).append .nil,
    history.pair.wordEntry.append [],history.pair.boolEntry.append []⟩,?_⟩⟩
  exact { history.captured with
    member := List.mem_append_left [] history.captured.member
    read := heapEq.symm ▸ allocated.preserves_read history.captured.read }

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedSelectedHandleObserved
/-! The observed result of the already planned independent Source call retains
all exported functions at its exact returned Source/native heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {first : InitialForward selected shape flag started callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {retained : first.Retained session entries}
  {entry : Entry} {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
  {call : CellAwarePublicHandleStart.StartedCall session entry.handle argument runOptions.inputValidationFuel}

/-- No result of the current target is used to construct the independent call.
Its actual completion identifies the same final store by native determinism. -/
theorem HandleSourcePlan.observed_selected_retained {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : HandleSourcePlan first retained entry call parameter result sourceArgument value after)
    (typing : OriginalTyping fixture.original)
    (cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions)
    (origins : CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entries)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    ∃ continued : first.Retained returned.session entries,
      continued.state.heap = after ∧
      CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
        continued.state.mapping continued.state.world entries := by
  obtain ⟨sidecar,_issued,_selected⟩ := selected.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size (.value plan.trace)
  have metadata : SourceCoreRawMetadata.Extends plan.start.encodedValues.registry
      plan.ready.receiving.result.context.registry := by
    rw [plan.ready.contextAt]
    exact .refl _
  obtain ⟨native,store,mapping,world,required,run,resultAt⟩ :=
    CellAwareCheckedPublicRetainedMaterializedForward.source_has_sufficient_fuel
      (invocation := RecursiveStageRegistry.scope sidecar [] selected.packet.header.function)
      first.functions callableProfile plan.ready.issued plan.ready.receiving.result.extension
      (typing.checked_registry cache)
      plan.ready.history.semantic entry plan.member plan.entryType plan.sourceEq plan.materialized plan.input
      plan.start.started plan.start.parameterView metadata (.singleton sourceArgument) plan.arity measured
  obtain ⟨actual,generation,reached,_exported,atReturned,_related,history,registry,exportsReady⟩ :=
    CellAwarePublicDirectObservedOutput.after_success _ _ plan.start.started
      (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt) retained.exportsReady
      plan.start.atCheckpoint resultAt (run required (Nat.le_refl _)) resumed plan.ready.history
  exact ⟨⟨{
    artifact := retained.state.artifact, session := actual.session,
    mapping := mapping, world := world, heap := after, store := store, caller := reached,
    atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
    receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
    registry := registry, history := history
    },exportsReady⟩,rfl,origins.extend resultAt.2.2.1 resultAt.2.2.2.1⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportHandleSteps
/-! Each concrete retained handle receives its own Source call plan. Actual
returned sessions keep all earlier entries and the saved capture cell. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicHandleStart (StartedCall)

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle handle : SourceCorePublicValues.Handle} {seed : Word}

/-- Retargeting an equal retained handle keeps the exact original checkpoint. -/
def atEntry {entry : Entry} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (same : entry.handle = handle) (call : StartedCall session handle argument fuel) :
    StartedCall session entry.handle argument fuel :=
  ⟨call.checkpoint,by rw [same]; exact call.accepted⟩

structure IdentityPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry history.pair.entries handle parameter result)
    (argument : SourceCorePublicValues.Value) (sourceArgument : Dynamic.Value)
    (call : StartedCall session handle argument runOptions.inputValidationFuel) where
  environment : Dynamic.Environment
  copied : Dynamic.Heap
  copy : Dynamic.EnvironmentCopies (identity.source.applySubstitution identity.substitution) identity.captured
    history.pair.retained.state.heap environment copied
  plan : HandleSourcePlan context.first history.pair.retained identity.entry (atEntry identity.handleEq call)
    parameter result sourceArgument sourceArgument
    ⟨copied.cells ++
      [{type := (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body, value := some sourceArgument}]⟩

theorem FullHistory.plan_identity (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry history.pair.entries handle parameter result)
    {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input history.pair.entries context.selected.packet.header.function.context
      parameter argument sourceArgument)
    (call : StartedCall session handle argument runOptions.inputValidationFuel) :
    Nonempty (IdentityPlan history identity argument sourceArgument call) := by
  obtain ⟨environment, copied, copy, ⟨plan⟩⟩ := identity_plan context.first history.pair.retained identity.entry
    (atEntry identity.handleEq call) identity.member identity.entryType (history.pair.origins identity.entry identity.member)
    input identity.shape identity.definitionContext identity.captured identity.substitution identity.evidence
    identity.sourceEq observed.typing
  exact ⟨⟨environment, copied, copy, plan⟩⟩

theorem IdentityPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {parameter result : TypeSystem.Ty} {identity : IdentityEntry history.pair.entries handle parameter result}
    {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
    {call : StartedCall session handle argument runOptions.inputValidationFuel}
    (planned : IdentityPlan history identity argument sourceArgument call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨continued,heapEq,origins⟩ := planned.plan.observed_selected_retained observed.typing observed.cache history.pair.origins resumed
  have allocated : Dynamic.Heap.Allocates planned.copied
      (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body (some sourceArgument)
      ⟨planned.copied.cells.length⟩
      ⟨planned.copied.cells ++
        [{type := (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body, value := some sourceArgument}]⟩ := .append
  exact ⟨⟨⟨_,continued,origins,history.pair.wordEntry,history.pair.boolEntry⟩,
    {history.captured with
      read := heapEq.symm ▸ allocated.preserves_read (planned.copy.preserves_read history.captured.read)}⟩⟩

structure CapturedPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    (flag : Bool) (call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel) where
  environment : Dynamic.Environment
  copied : Dynamic.Heap
  copy : Dynamic.EnvironmentCopies (history.captured.source.applySubstitution history.captured.substitution)
    history.captured.captured history.pair.retained.state.heap environment copied
  plan : HandleSourcePlan context.first history.pair.retained history.captured.entry (atEntry history.captured.handleEq call)
    .bool .word (.bool flag) (.word seed)
    ⟨copied.cells ++
      [{type := (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body, value := some (.bool flag)}]⟩

theorem FullHistory.plan_captured (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    (flag : Bool) (call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel) :
    Nonempty (CapturedPlan history flag call) := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input history.pair.entries
      context.selected.packet.header.function.context .bool (.bool flag) (.bool flag) :=
    .data ⟨.bool flag,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool flag⟩ ⟨.bool flag,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool flag⟩
  obtain ⟨environment, copied, copy, ⟨plan⟩⟩ := captured_plan context.first history.pair.retained history.captured.entry
    (atEntry history.captured.handleEq call) history.captured.member history.captured.entryType
    (history.pair.origins history.captured.entry history.captured.member) input history.captured.shape
    history.captured.definitionContext history.captured.captured history.captured.substitution history.captured.evidence
    history.captured.sourceEq history.captured.lookup history.captured.read rfl rfl observed.typing
  exact ⟨⟨environment, copied, copy, plan⟩⟩

theorem CapturedPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {flag : Bool} {call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel}
    (planned : CapturedPlan history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨continued,heapEq,origins⟩ := planned.plan.observed_selected_retained observed.typing observed.cache history.pair.origins resumed
  have allocated : Dynamic.Heap.Allocates planned.copied
      (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body (some (.bool flag))
      ⟨planned.copied.cells.length⟩
      ⟨planned.copied.cells ++
        [{type := (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body, value := some (.bool flag)}]⟩ := .append
  exact ⟨⟨⟨_,continued,origins,history.pair.wordEntry,history.pair.boolEntry⟩,
    {history.captured with
      read := heapEq.symm ▸ allocated.preserves_read (planned.copy.preserves_read history.captured.read)}⟩⟩

end Tests.SourceCoreGeneralizedExport
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedExportRuntime
/-! The unchanged complete program is run once. Every target resume follows an
independent Source plan; every next plan consumes the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport.SourcePublicRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

def Certified (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) : Prop :=
  ∃ context : Context observed, Nonempty (FullHistory context session wordHandle boolHandle captureHandle seed)

def WordPlanned (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.wordEntry (.word value) (.word value) call)

theorem plan_word (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) :
    WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.wordEntry
    (.data ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩ ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩) call⟩

theorem word_retained {value : Word}
    {call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel}
    (planned : WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def BoolPlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.boolEntry (.bool value) (.bool value) call)

theorem plan_bool (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) :
    BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.boolEntry
    (.data ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩ ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩) call⟩

theorem bool_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel}
    (planned : BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def CapturePlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (CapturedPlan history value call)

theorem plan_capture (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) :
    CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_captured value call⟩

theorem capture_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel}
    (planned : CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions) := do
  match accepted : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) :
    IO (CellAwarePublicHandleStart.StartedCall session handle argument runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle argument runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified generalized export call did not succeed")

private structure PairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  wordHandle : SourceCorePublicValues.Handle
  boolHandle : SourceCorePublicValues.Handle
  same : returned.value = .product (.function wordHandle) (.function boolHandle)

private def pairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (PairOutput returned) := do
  match same : returned.value with
  | .product (.function first) (.function second) => return ⟨first,second,same⟩
  | _ => throw (IO.userError "Source-certified generalized pair output changed")

private structure FunctionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .function handle

private def functionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (FunctionOutput returned) := do
  match same : returned.value with
  | .function handle => return ⟨handle,same⟩
  | _ => throw (IO.userError "Source-certified captured output changed")

/-- All original rows remain compiled and profiled. Each `resume` consumes a
plan built from independent Source semantics at the actual preceding heap. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.make.original.key [.bool true]
  have firstPlan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.make),
      Nonempty (InitialForward selected observed.makeShape true firstStart observed.callableProfile) := by
    obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.typing.wellFormed
    obtain ⟨selected⟩ := whole.select observed.make
    exact ⟨whole,selected,initial_from_source selected observed.makeShape true observed.typing firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let pair ← pairOutput firstResult.val
  have pairHistory : ∃ context : Context observed,
      Nonempty (PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle) := by
    obtain ⟨whole,selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨whole,selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property pair.same⟩
  let seed := Word.ofNatModulo 29
  let captureCall ← namedCall firstResult.val.session observed.capture.original.key [.word seed]
  have capturePlan : ∃ (context : Context observed)
      (history : PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle),
      Nonempty (CapturePlan history seed captureCall) := by
    obtain ⟨context,⟨history⟩⟩ := pairHistory
    exact ⟨context,history,history.plan_capture seed captureCall⟩
  let captureResult ← resume captureCall.checkpoint
  let captured ← functionOutput captureResult.val
  have capturedHistory : Certified observed captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := capturePlan
    exact ⟨context,plan.collected captureResult.property captured.same⟩
  let tickCall ← namedCall captureResult.val.session observed.tick.original.key [.bool false]
  have tickPlan : ∃ (context : Context observed)
      (history : FullHistory context captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed),
      Nonempty (TickPlan history false tickCall) := by
    obtain ⟨context,⟨history⟩⟩ := capturedHistory
    exact ⟨context,history,history.plan_tick false tickCall⟩
  let tickResult ← resume tickCall.checkpoint
  have tickHistory : Certified observed tickResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := tickPlan
    exact ⟨context,plan.retained tickResult.property⟩
  require (tickResult.val.value == .bool false) "Source-certified intervening result changed"
  let wordCall ← handleCall tickResult.val.session pair.wordHandle (.word (Word.ofNatModulo 47))
  have wordPlan := plan_word observed tickHistory (Word.ofNatModulo 47) wordCall
  let wordResult ← resume wordCall.checkpoint
  have wordHistory := word_retained observed wordPlan wordResult.property
  require (wordResult.val.value == .word (Word.ofNatModulo 47)) "Source-certified Word handle result changed"
  let boolCall ← handleCall wordResult.val.session pair.boolHandle (.bool true)
  have boolPlan := plan_bool observed wordHistory true boolCall
  let boolResult ← resume boolCall.checkpoint
  have boolHistory := bool_retained observed boolPlan boolResult.property
  require (boolResult.val.value == .bool true) "Source-certified Bool handle result changed"
  let savedCall ← handleCall boolResult.val.session captured.handle (.bool false)
  have savedPlan := plan_capture observed boolHistory false savedCall
  let savedResult ← resume savedCall.checkpoint
  have savedHistory := capture_retained observed savedPlan savedResult.property
  require (savedResult.val.value == .word seed) "Source-certified captured value changed"
  let repeatCall ← handleCall savedResult.val.session pair.wordHandle (.word (Word.ofNatModulo 61))
  have repeatPlan := plan_word observed savedHistory (Word.ofNatModulo 61) repeatCall
  let repeatResult ← resume repeatCall.checkpoint
  have _finalHistory := word_retained observed repeatPlan repeatResult.property
  require (repeatResult.val.value == .word (Word.ofNatModulo 61)) "Source-certified repeated handle changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,captureResult.val.session.heapSize,
    tickResult.val.session.heapSize,wordResult.val.session.heapSize,boolResult.val.session.heapSize,
    savedResult.val.session.heapSize,repeatResult.val.session.heapSize]
  require (heaps == [4,13,22,25,31,37,43,49]) "Source-certified exported handle heaps changed"
  IO.println "GENERALIZED_EXPORTED_SOURCE_PUBLIC: originals3/cache3/typed3/profile3; make/capture/tick/Word/Bool/captured/reuse"
  IO.println s!"GENERALIZED_EXPORTED_SOURCE_HEAPS: {heaps}"
  IO.println "GENERALIZED_EXPORTED_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreGeneralizedExport.SourcePublicRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedNamedSelectedRuntime
/-! The unchanged complete program is run once. Every target resume follows an
independent Source plan; every next plan consumes the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport.SourcePublicNamedSelectedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

def Certified (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) : Prop :=
  ∃ context : Context observed, Nonempty (FullHistory context session wordHandle boolHandle captureHandle seed)

def WordPlanned (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.wordEntry (.word value) (.word value) call)

theorem plan_word (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) :
    WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.wordEntry
    (.data ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩ ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩) call⟩

theorem word_retained {value : Word}
    {call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel}
    (planned : WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def BoolPlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.boolEntry (.bool value) (.bool value) call)

theorem plan_bool (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) :
    BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.boolEntry
    (.data ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩ ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩) call⟩

theorem bool_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel}
    (planned : BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def CapturePlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (CapturedPlan history value call)

theorem plan_capture (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) :
    CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_captured value call⟩

theorem capture_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel}
    (planned : CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions) := do
  match accepted : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) :
    IO (CellAwarePublicHandleStart.StartedCall session handle argument runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle argument runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified generalized export call did not succeed")

private structure PairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  wordHandle : SourceCorePublicValues.Handle
  boolHandle : SourceCorePublicValues.Handle
  same : returned.value = .product (.function wordHandle) (.function boolHandle)

private def pairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (PairOutput returned) := do
  match same : returned.value with
  | .product (.function first) (.function second) => return ⟨first,second,same⟩
  | _ => throw (IO.userError "Source-certified generalized pair output changed")

private structure FunctionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .function handle

private def functionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (FunctionOutput returned) := do
  match same : returned.value with
  | .function handle => return ⟨handle,same⟩
  | _ => throw (IO.userError "Source-certified captured output changed")

/-- All original rows remain compiled and profiled. Each `resume` consumes a
plan built from independent Source semantics at the actual preceding heap. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.make.original.key [.bool true]
  have firstPlan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.make),
      Nonempty (InitialForward selected observed.makeShape true firstStart observed.callableProfile) := by
    obtain ⟨whole⟩ := observed.fixture.inventory_selected observed.cache observed.typing.selected_bodies
    obtain ⟨selected⟩ := whole.select observed.make
    exact ⟨whole,selected,initial_from_source_selected selected observed.makeShape true (observed.typing.checked_registry observed.cache).namedSupport firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let pair ← pairOutput firstResult.val
  have pairHistory : ∃ context : Context observed,
      Nonempty (PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle) := by
    obtain ⟨whole,selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨whole,selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property pair.same⟩
  let seed := Word.ofNatModulo 29
  let captureCall ← namedCall firstResult.val.session observed.capture.original.key [.word seed]
  have capturePlan : ∃ (context : Context observed)
      (history : PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle),
      Nonempty (CapturePlan history seed captureCall) := by
    obtain ⟨context,⟨history⟩⟩ := pairHistory
    exact ⟨context,history,history.plan_capture seed captureCall⟩
  let captureResult ← resume captureCall.checkpoint
  let captured ← functionOutput captureResult.val
  have capturedHistory : Certified observed captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := capturePlan
    exact ⟨context,plan.collected captureResult.property captured.same⟩
  let tickCall ← namedCall captureResult.val.session observed.tick.original.key [.bool false]
  have tickPlan : ∃ (context : Context observed)
      (history : FullHistory context captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed),
      Nonempty (TickPlan history false tickCall) := by
    obtain ⟨context,⟨history⟩⟩ := capturedHistory
    exact ⟨context,history,history.plan_tick false tickCall⟩
  let tickResult ← resume tickCall.checkpoint
  have tickHistory : Certified observed tickResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := tickPlan
    exact ⟨context,plan.retained tickResult.property⟩
  require (tickResult.val.value == .bool false) "Source-certified intervening result changed"
  let wordCall ← handleCall tickResult.val.session pair.wordHandle (.word (Word.ofNatModulo 47))
  have wordPlan := plan_word observed tickHistory (Word.ofNatModulo 47) wordCall
  let wordResult ← resume wordCall.checkpoint
  have wordHistory := word_retained observed wordPlan wordResult.property
  require (wordResult.val.value == .word (Word.ofNatModulo 47)) "Source-certified Word handle result changed"
  let boolCall ← handleCall wordResult.val.session pair.boolHandle (.bool true)
  have boolPlan := plan_bool observed wordHistory true boolCall
  let boolResult ← resume boolCall.checkpoint
  have boolHistory := bool_retained observed boolPlan boolResult.property
  require (boolResult.val.value == .bool true) "Source-certified Bool handle result changed"
  let savedCall ← handleCall boolResult.val.session captured.handle (.bool false)
  have savedPlan := plan_capture observed boolHistory false savedCall
  let savedResult ← resume savedCall.checkpoint
  have savedHistory := capture_retained observed savedPlan savedResult.property
  require (savedResult.val.value == .word seed) "Source-certified captured value changed"
  let repeatCall ← handleCall savedResult.val.session pair.wordHandle (.word (Word.ofNatModulo 61))
  have repeatPlan := plan_word observed savedHistory (Word.ofNatModulo 61) repeatCall
  let repeatResult ← resume repeatCall.checkpoint
  have _finalHistory := word_retained observed repeatPlan repeatResult.property
  require (repeatResult.val.value == .word (Word.ofNatModulo 61)) "Source-certified repeated handle changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,captureResult.val.session.heapSize,
    tickResult.val.session.heapSize,wordResult.val.session.heapSize,boolResult.val.session.heapSize,
    savedResult.val.session.heapSize,repeatResult.val.session.heapSize]
  require (heaps == [4,13,22,25,31,37,43,49]) "Source-certified exported handle heaps changed"
  IO.println "GENERALIZED_NAMED_SELECTED_SOURCE_PUBLIC: originals3/cache3/selected-body-typing3/checked-registry; make/capture/tick/Word/Bool/captured/reuse"
  IO.println s!"GENERALIZED_NAMED_SELECTED_SOURCE_HEAPS: {heaps}"
  IO.println "GENERALIZED_NAMED_SELECTED_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreGeneralizedExport.SourcePublicNamedSelectedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedSelectedRuntime
/-! The unchanged complete program is run once. Every target resume follows an
independent Source plan; every next plan consumes the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport.SourcePublicSelectedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

def Certified (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) : Prop :=
  ∃ context : Context observed, Nonempty (FullHistory context session wordHandle boolHandle captureHandle seed)

def WordPlanned (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.wordEntry (.word value) (.word value) call)

theorem plan_word (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Word)
    (call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel) :
    WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.wordEntry
    (.data ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩ ⟨.word value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word value⟩) call⟩

theorem word_retained {value : Word}
    {call : CellAwarePublicHandleStart.StartedCall session wordHandle (.word value) runOptions.inputValidationFuel}
    (planned : WordPlanned observed (boolHandle := boolHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def BoolPlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (IdentityPlan history history.pair.boolEntry (.bool value) (.bool value) call)

theorem plan_bool (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel) :
    BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_identity history.pair.boolEntry
    (.data ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩ ⟨.bool value,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool value⟩) call⟩

theorem bool_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session boolHandle (.bool value) runOptions.inputValidationFuel}
    (planned : BoolPlanned observed (wordHandle := wordHandle) (captureHandle := captureHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

def CapturePlanned (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : FullHistory context session wordHandle boolHandle captureHandle seed),
    Nonempty (CapturedPlan history value call)

theorem plan_capture (certified : Certified observed session wordHandle boolHandle captureHandle seed) (value : Bool)
    (call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel) :
    CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_captured value call⟩

theorem capture_retained {value : Bool}
    {call : CellAwarePublicHandleStart.StartedCall session captureHandle (.bool value) runOptions.inputValidationFuel}
    (planned : CapturePlanned observed (wordHandle := wordHandle) (boolHandle := boolHandle) (seed := seed) value call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session wordHandle boolHandle captureHandle seed := by
  obtain ⟨context,history,⟨plan⟩⟩ := planned
  exact ⟨context,plan.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions) := do
  match accepted : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) :
    IO (CellAwarePublicHandleStart.StartedCall session handle argument runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle argument runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified generalized export call did not succeed")

private structure PairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  wordHandle : SourceCorePublicValues.Handle
  boolHandle : SourceCorePublicValues.Handle
  same : returned.value = .product (.function wordHandle) (.function boolHandle)

private def pairOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (PairOutput returned) := do
  match same : returned.value with
  | .product (.function first) (.function second) => return ⟨first,second,same⟩
  | _ => throw (IO.userError "Source-certified generalized pair output changed")

private structure FunctionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .function handle

private def functionOutput {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (FunctionOutput returned) := do
  match same : returned.value with
  | .function handle => return ⟨handle,same⟩
  | _ => throw (IO.userError "Source-certified captured output changed")

/-- All original rows remain compiled and profiled. Each `resume` consumes a
plan built from independent Source semantics at the actual preceding heap. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.make.original.key [.bool true]
  have firstPlan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.make),
      Nonempty (InitialForward selected observed.makeShape true firstStart observed.callableProfile) := by
    obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.typing.wellFormed
    obtain ⟨selected⟩ := whole.select observed.make
    exact ⟨whole,selected,initial_from_source selected observed.makeShape true observed.typing firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let pair ← pairOutput firstResult.val
  have pairHistory : ∃ context : Context observed,
      Nonempty (PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle) := by
    obtain ⟨whole,selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨whole,selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property pair.same⟩
  let seed := Word.ofNatModulo 29
  let captureCall ← namedCall firstResult.val.session observed.capture.original.key [.word seed]
  have capturePlan : ∃ (context : Context observed)
      (history : PairHistory context firstResult.val.session pair.wordHandle pair.boolHandle),
      Nonempty (CapturePlan history seed captureCall) := by
    obtain ⟨context,⟨history⟩⟩ := pairHistory
    exact ⟨context,history,history.plan_capture seed captureCall⟩
  let captureResult ← resume captureCall.checkpoint
  let captured ← functionOutput captureResult.val
  have capturedHistory : Certified observed captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := capturePlan
    exact ⟨context,plan.collected captureResult.property captured.same⟩
  let tickCall ← namedCall captureResult.val.session observed.tick.original.key [.bool false]
  have tickPlan : ∃ (context : Context observed)
      (history : FullHistory context captureResult.val.session pair.wordHandle pair.boolHandle captured.handle seed),
      Nonempty (TickPlan history false tickCall) := by
    obtain ⟨context,⟨history⟩⟩ := capturedHistory
    exact ⟨context,history,history.plan_tick false tickCall⟩
  let tickResult ← resume tickCall.checkpoint
  have tickHistory : Certified observed tickResult.val.session pair.wordHandle pair.boolHandle captured.handle seed := by
    obtain ⟨context,history,⟨plan⟩⟩ := tickPlan
    exact ⟨context,plan.retained tickResult.property⟩
  require (tickResult.val.value == .bool false) "Source-certified intervening result changed"
  let wordCall ← handleCall tickResult.val.session pair.wordHandle (.word (Word.ofNatModulo 47))
  have wordPlan := plan_word observed tickHistory (Word.ofNatModulo 47) wordCall
  let wordResult ← resume wordCall.checkpoint
  have wordHistory := word_retained observed wordPlan wordResult.property
  require (wordResult.val.value == .word (Word.ofNatModulo 47)) "Source-certified Word handle result changed"
  let boolCall ← handleCall wordResult.val.session pair.boolHandle (.bool true)
  have boolPlan := plan_bool observed wordHistory true boolCall
  let boolResult ← resume boolCall.checkpoint
  have boolHistory := bool_retained observed boolPlan boolResult.property
  require (boolResult.val.value == .bool true) "Source-certified Bool handle result changed"
  let savedCall ← handleCall boolResult.val.session captured.handle (.bool false)
  have savedPlan := plan_capture observed boolHistory false savedCall
  let savedResult ← resume savedCall.checkpoint
  have savedHistory := capture_retained observed savedPlan savedResult.property
  require (savedResult.val.value == .word seed) "Source-certified captured value changed"
  let repeatCall ← handleCall savedResult.val.session pair.wordHandle (.word (Word.ofNatModulo 61))
  have repeatPlan := plan_word observed savedHistory (Word.ofNatModulo 61) repeatCall
  let repeatResult ← resume repeatCall.checkpoint
  have _finalHistory := word_retained observed repeatPlan repeatResult.property
  require (repeatResult.val.value == .word (Word.ofNatModulo 61)) "Source-certified repeated handle changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,captureResult.val.session.heapSize,
    tickResult.val.session.heapSize,wordResult.val.session.heapSize,boolResult.val.session.heapSize,
    savedResult.val.session.heapSize,repeatResult.val.session.heapSize]
  require (heaps == [4,13,22,25,31,37,43,49]) "Source-certified exported handle heaps changed"
  IO.println "GENERALIZED_SELECTED_SOURCE_PUBLIC: originals3/cache3/selected-body-typing3/checked-registry; make/capture/tick/Word/Bool/captured/reuse"
  IO.println s!"GENERALIZED_SELECTED_SOURCE_HEAPS: {heaps}"
  IO.println "GENERALIZED_SELECTED_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreGeneralizedExport.SourcePublicSelectedRuntime
end
