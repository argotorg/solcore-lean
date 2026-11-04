import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedProgramProfiles
import Solcore.Test.SourceSemantics.CoreLowering.Selected.Interleaved
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.Test.SourceSemantics.CoreLowering.Generalized.Export
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.Test.SourceSemantics.CoreLowering.Selected.GeneralizedSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedForward
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicImperativeNamedContinuation

/-!
# Mixed control tests

Mixed bodies with conditionals and imperative statements.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalProbe
/-! One unchanged original body combines a conditional, a generalized identity,
and a returned builtin function value. This probe observes acceptance and runtime;
independent Source and public correspondence use the same unchanged workspace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function conditionalPair(flag: Bool) returns (Bool, function(Word) returns (integer)) {",
    "  let f = lam(value) { return value; };",
    "  return (flag ? f(true) : f(false), wordToInteger);",
    "}" ]}] }
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
  let program ← get "check mixed conditional" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed conditional" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed conditional cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed conditional" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed conditional" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "builtin factory" (← initial.run root.key [.bool true] runOptions)
  let .product (.bool true) (.function handle) := first.value | throw (IO.userError "builtin factory output")
  let invoked ← succeeded "returned builtin" (← first.session.invokePacked handle (.word (word 17)) runOptions)
  require (invoked.value == .integer 17) "returned builtin result"
  let second ← succeeded "factory reused" (← invoked.session.run root.key [.bool false] runOptions)
  let .product (.bool false) (.function _) := second.value | throw (IO.userError "reused factory output")
  IO.println s!"MIXED_CONDITIONAL_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,invoked.session.heapSize,second.session.heapSize]}"
  IO.println "MIXED_CONDITIONAL_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_CONDITIONAL_PROBE_PASS"

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
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
      | none => throw (IO.userError "mixed conditional artifact absent")
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
    | throw (IO.userError "mixed conditional original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed conditional original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed conditional global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed conditional substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed conditional ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed conditional ordinary parameters"
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
    | _ => throw (IO.userError "mixed conditional unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed conditional complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed conditional complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed conditional complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "conditionalPair"
  IO.println "MIXED_CONDITIONAL_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.profile {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    Nonempty (CellAwareNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeProbe
/-! One original body mixes generalized locals, ordinary declarations, a block,
branching and discarded calls. This probe observes actual acceptance and runtime;
independent Source and public correspondence use the same unchanged workspace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed(flag: Bool) returns (Word, Bool) {",
    "  let f = lam(value) { return value; };",
    "  {",
    "    let first = f(11);",
    "    if (flag) {",
    "      let g = lam(value) { return value; };",
    "      let chosen = g(first);",
    "      f(chosen);",
    "    } else { f(false); }",
    "  }",
    "  return (f(17), f(flag));",
    "}" ]}] }
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
  let program ← get "check mixed imperative" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed imperative" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed imperative cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed imperative" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed imperative" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "true branch" (← initial.run root.key [.bool true] runOptions)
  require (first.value == .product (.word (word 17)) (.bool true)) "mixed true result"
  let second ← succeeded "false branch" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == .product (.word (word 17)) (.bool false)) "mixed false result"
  let repeated ← succeeded "true branch reused" (← second.session.run root.key [.bool true] runOptions)
  require (repeated.value == .product (.word (word 17)) (.bool true)) "mixed reused result"
  IO.println s!"MIXED_IMPERATIVE_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,repeated.session.heapSize]}"
  IO.println "MIXED_IMPERATIVE_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_IMPERATIVE_PROBE_PASS"

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
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
      | none => throw (IO.userError "mixed imperative artifact absent")
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
    | throw (IO.userError "mixed imperative original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed imperative original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed imperative global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed imperative substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed imperative ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed imperative ordinary parameters"
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
    | _ => throw (IO.userError "mixed imperative unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareImperativeNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed imperative complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed imperative complete compiler cache"
  let some profiles := CellAwareImperativeNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed imperative complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "mixed"
  IO.println "MIXED_IMPERATIVE_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.profile {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    Nonempty (CellAwareImperativeNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSourceState
/-! The independent Source trace carries its own typing and lexical state.
Preservation is used only after constructing an actual Source step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Frontend SourceInference SourceSemantics

structure SourceState (program : SourceSemantics.Program) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context source
  covers : evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  heapTyped : Dynamic.HeapWellTyped context heap

theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

theorem SourceState.after_statement {program : SourceSemantics.Program} {source : TypedSource}
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program) {control : ControlContext} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts)
    (trace : Dynamic.StatementExecutes program context evidence source environment before id final (.fallthrough next) after) :
    SourceState program source final evidence next after := by
  have kept := wellFormed.wholeLanguagePreservation.statements _ _ _ _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped (StatementsHaveType.singleton typed)
    (Dynamic.StatementsExecute.cons trace .nil)
  have fields := Dynamic.StatementHasType.runtimeContextFields typed
  cases kept.outcome_typed with
  | fallthrough locals =>
    exact ⟨state.runtime.transport fields, fields.covers state.covers, locals,
      kept.heap_typed.transportClosed fields.signatures state.runtime.closed
        (fields.targetClosed state.runtime.closed) state.runtime.variables_closed
        (fields.targetResidualVariablesOpen state.runtime.residual_variables_open)⟩

theorem SourceState.after_expression {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program) {id : ExpressionId} {type : TypeSystem.Ty} {value : Dynamic.Value}
    (typed : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    SourceState program source context evidence environment after := by
  have kept := wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped typed trace
  exact ⟨state.runtime, state.covers, state.locals.mono kept.heap_extends, kept.heap_typed⟩

/-- Exact append-only Source heaps keep earlier initialized cells readable. -/
def HeapAppends (before after : Dynamic.Heap) : Prop := ∃ cells, after.cells = before.cells ++ cells

theorem HeapAppends.refl (heap : Dynamic.Heap) : HeapAppends heap heap := ⟨[], by simp⟩
theorem HeapAppends.trans {first middle last : Dynamic.Heap}
    (left : HeapAppends first middle) (right : HeapAppends middle last) : HeapAppends first last := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right
  exact ⟨a ++ b, by rw [hb,ha,List.append_assoc]⟩

theorem HeapAppends.read {before after : Dynamic.Heap} (append : HeapAppends before after)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := by
  obtain ⟨cells, same⟩ := append
  cases read with
  | intro selected =>
    apply Dynamic.Heap.Reads.intro
    rw [same]
    exact selected.append_left

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSource
/-! Exact original occurrences for nested lexical blocks and conditional
identity calls. The observer below validates every relationship in the graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)

structure StatementAt (source : TypedSource) (form : StatementForm) where
  node : StatementNode
  found : source.lookupStatement? node.id = some node
  formEq : node.form = form

structure BooleanAt (source : TypedSource) (value : Bool) where
  node : ExpressionNode
  name : String
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference name (.builtinBoolean value)
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  first : TypedBinder
  g : IdentityShape source
  chosen : TypedBinder
  eleven : WordNode source
  seventeen : WordNode source
  falseNode : BooleanAt source false
  condition : Tests.SourceCoreNamedBranch.Read source flag .bool
  firstRead : Tests.SourceCoreNamedBranch.Read source first .word
  chosenRead : Tests.SourceCoreNamedBranch.Read source chosen .word
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  firstCall : CallShape source f.binder eleven.node.id .word
  chosenCall : CallShape source g.binder firstRead.node.id .word
  thenCall : CallShape source f.binder chosenRead.node.id .word
  elseCall : CallShape source f.binder falseNode.node.id .bool
  finalWordCall : CallShape source f.binder seventeen.node.id .word
  finalBoolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  firstLet : StatementAt source (.letDecl first (some firstCall.node.id))
  gLet : StatementAt source (.letDecl g.binder (some g.lambda.id))
  chosenLet : StatementAt source (.letDecl chosen (some chosenCall.node.id))
  thenDiscard : StatementAt source (.expression thenCall.node.id true)
  elseDiscard : StatementAt source (.expression elseCall.node.id true)
  branch : StatementAt source (.ifThen condition.node.id
    [gLet.node.id, chosenLet.node.id, thenDiscard.node.id] (some [elseDiscard.node.id]))
  block : StatementAt source (.block [firstLet.node.id, branch.node.id])
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [finalWordCall.node.id, finalBoolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,.statement block.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  firstScheme : first.scheme = .mono .word
  chosenScheme : chosen.scheme = .mono .word
  elevenValue : eleven.resolution.rawValue = 11
  seventeenValue : seventeen.resolution.rawValue = 17
  fFlag : f.binder.id ≠ flag.id
  firstF : first.id ≠ f.binder.id
  firstFlag : first.id ≠ flag.id
  gFirst : g.binder.id ≠ first.id
  gF : g.binder.id ≠ f.binder.id
  gFlag : g.binder.id ≠ flag.id
  chosenG : chosen.id ≠ g.binder.id
  chosenFirst : chosen.id ≠ first.id
  chosenF : chosen.id ≠ f.binder.id
  chosenFlag : chosen.id ≠ flag.id

private def observed_variant (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def statementAt (source : TypedSource) (node : StatementNode) (form : StatementForm) :
    IO (StatementAt source form) := do
  let ⟨found⟩ ← observed_variant (source.lookupStatement? node.id = some node) "imperative statement identity"
  let ⟨formEq⟩ ← observed_variant (node.form = form) "imperative original statement form"
  return ⟨node,found,formEq⟩

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed_variant (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed_variant (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed_variant (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed_variant (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed_variant (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed_variant (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed_variant (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed_variant (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed_variant (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed_variant (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed_variant (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed_variant (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed_variant (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed_variant (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed_variant (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed_variant (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed_variant (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "imperative input")
  let .expression fRead ::.statement fReturn ::.expression fLambda ::.statement fInit ::
       .expression elevenNode ::.expression firstCallee ::.expression firstCallNode ::.statement firstInit ::
       .expression conditionNode ::.expression gRead ::.statement gReturn ::.expression gLambda ::.statement gInit ::
       .expression firstReadNode ::.expression chosenCallee ::.expression chosenCallNode ::.statement chosenInit ::
       .expression chosenReadNode ::.expression thenCallee ::.expression thenCallNode ::.statement thenStmt ::
       .expression falseExpr ::.expression elseCallee ::.expression elseCallNode ::.statement elseStmt ::
       .statement branchNode ::.statement blockNode ::
       .expression seventeenNode ::.expression finalWordCallee ::.expression finalWordNode ::
       .expression flagNode ::.expression finalBoolCallee ::.expression finalBoolNode ::
       .expression tuple ::.statement returnNode :: [] := source.nodes | throw (IO.userError "imperative original graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "imperative f declaration")
  let .letDecl first _ := firstInit.form | throw (IO.userError "imperative first declaration")
  let .letDecl gBinder _ := gInit.form | throw (IO.userError "imperative g declaration")
  let .letDecl chosen _ := chosenInit.form | throw (IO.userError "imperative chosen declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let g ← identity source gBinder gLambda gRead gReturn
  let eleven ← wordNode source elevenNode
  let seventeen ← wordNode source seventeenNode
  let .reference falseName (.builtinBoolean false) := falseExpr.form | throw (IO.userError "imperative false")
  let ⟨falseFound⟩ ← observed_variant (source.lookupExpression? falseExpr.id = some falseExpr) "false identity"
  let ⟨falseForm⟩ ← observed_variant (falseExpr.form = .reference falseName (.builtinBoolean false)) "false form"
  let ⟨falseRequirements⟩ ← observed_variant (falseExpr.requirements = []) "false requirements"
  let ⟨falseCoercions⟩ ← observed_variant (falseExpr.coercions = []) "false coercions"
  let falseNode : BooleanAt source false := ⟨falseExpr,falseName,falseFound,falseForm,falseRequirements,falseCoercions⟩
  let condition ← Tests.SourceCoreNamedBranch.observeRead source flag conditionNode .bool
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead source first firstReadNode .word
  let chosenRead ← Tests.SourceCoreNamedBranch.observeRead source chosen chosenReadNode .word
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let firstCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder eleven.node.id .word firstCallee firstCallNode
  let chosenCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source g.binder firstRead.node.id .word chosenCallee chosenCallNode
  let thenCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder chosenRead.node.id .word thenCallee thenCallNode
  let elseCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool elseCallee elseCallNode
  let finalWordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder seventeen.node.id .word finalWordCallee finalWordNode
  let finalBoolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool finalBoolCallee finalBoolNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let firstLet ← statementAt source firstInit (.letDecl first (some firstCall.node.id))
  let gLet ← statementAt source gInit (.letDecl g.binder (some g.lambda.id))
  let chosenLet ← statementAt source chosenInit (.letDecl chosen (some chosenCall.node.id))
  let thenDiscard ← statementAt source thenStmt (.expression thenCall.node.id true)
  let elseDiscard ← statementAt source elseStmt (.expression elseCall.node.id true)
  let branch ← statementAt source branchNode (.ifThen condition.node.id [gLet.node.id,chosenLet.node.id,thenDiscard.node.id] (some [elseDiscard.node.id]))
  let block ← statementAt source blockNode (.block [firstLet.node.id,branch.node.id])
  let ⟨tupleFound⟩ ← observed_variant (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed_variant (tuple.form = .tuple [finalWordCall.node.id,finalBoolCall.node.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed_variant (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed_variant (tuple.coercions = []) "tuple coercions"
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨inputs⟩ ← observed_variant (source.inputs = [flag]) "imperative source inputs"
  let ⟨roots⟩ ← observed_variant (source.roots = [.statement fLet.node.id,.statement block.node.id,.statement returned.node.id]) "imperative root order"
  let ⟨flagScheme⟩ ← observed_variant (flag.scheme = .mono .bool) "flag scheme"
  let ⟨firstScheme⟩ ← observed_variant (first.scheme = .mono .word) "first scheme"
  let ⟨chosenScheme⟩ ← observed_variant (chosen.scheme = .mono .word) "chosen scheme"
  let ⟨elevenValue⟩ ← observed_variant (eleven.resolution.rawValue = 11) "first literal"
  let ⟨seventeenValue⟩ ← observed_variant (seventeen.resolution.rawValue = 17) "final literal"
  let ⟨fFlag⟩ ← observed_variant (f.binder.id ≠ flag.id) "f/flag"
  let ⟨firstF⟩ ← observed_variant (first.id ≠ f.binder.id) "first/f"
  let ⟨firstFlag⟩ ← observed_variant (first.id ≠ flag.id) "first/flag"
  let ⟨gFirst⟩ ← observed_variant (g.binder.id ≠ first.id) "g/first"
  let ⟨gF⟩ ← observed_variant (g.binder.id ≠ f.binder.id) "g/f"
  let ⟨gFlag⟩ ← observed_variant (g.binder.id ≠ flag.id) "g/flag"
  let ⟨chosenG⟩ ← observed_variant (chosen.id ≠ g.binder.id) "chosen/g"
  let ⟨chosenFirst⟩ ← observed_variant (chosen.id ≠ first.id) "chosen/first"
  let ⟨chosenF⟩ ← observed_variant (chosen.id ≠ f.binder.id) "chosen/f"
  let ⟨chosenFlag⟩ ← observed_variant (chosen.id ≠ flag.id) "chosen/flag"
  return ⟨flag,f,first,g,chosen,eleven,seventeen,falseNode,condition,firstRead,chosenRead,flagRead,
    firstCall,chosenCall,thenCall,elseCall,finalWordCall,finalBoolCall,fLet,firstLet,gLet,chosenLet,thenDiscard,elseDiscard,
    branch,block,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,returned,inputs,roots,flagScheme,firstScheme,
    chosenScheme,elevenValue,seventeenValue,fFlag,firstF,firstFlag,gFirst,gF,gFlag,chosenG,chosenFirst,chosenF,chosenFlag⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSourceSteps
/-! Independent source steps expose the exact local cells and append order.
Closures capture by value: a generalized `let` copies the environment before
storing its descriptor, and each identity call copies the descriptor's
captures before allocating its parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)
open Tests.SourceSemanticsCaptureCopies

def StoredValue (binder : TypedBinder) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (value : Dynamic.Value) : Prop :=
  ∃ location cell, Dynamic.Environment.LooksUp environment binder.id location ∧
    Dynamic.Heap.Reads heap location cell ∧ cell.generalized = none ∧ cell.value = some value

def StoredIdentity {source : TypedSource} (shape : IdentityShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop :=
  ∃ definitionContext captured location cell,
    Dynamic.Environment.LooksUp environment shape.binder.id location ∧
    Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = some (shape.descriptor definitionContext captured) ∧
    Dynamic.RuntimeContextFields definitionContext context

/-- Copying a captured environment only appends cells. -/
theorem HeapAppends.of_copies (source : TypedSource) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    HeapAppends heap (copies source environment heap).2 :=
  copies_appends source environment heap

theorem HeapAppends.of_environmentCopies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after) :
    HeapAppends before after :=
  appends_of_copies copy

theorem StoredValue.mono {binder : TypedBinder} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value} (stored : StoredValue binder environment before value)
    (append : HeapAppends before after) : StoredValue binder environment after value := by
  rcases stored with ⟨location,cell,lookup,read,ordinary,contents⟩
  exact ⟨location,cell,lookup,append.read read,ordinary,contents⟩

theorem StoredValue.under {binder next : TypedBinder} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {value : Dynamic.Value} (stored : StoredValue binder environment heap value)
    (location : Dynamic.Location) (different : next.id ≠ binder.id) :
    StoredValue binder ((next.id,location) :: environment) heap value := by
  rcases stored with ⟨found,cell,lookup,read,ordinary,contents⟩
  exact ⟨found,cell,.tail different lookup,read,ordinary,contents⟩

theorem StoredIdentity.mono {source : TypedSource} {shape : IdentityShape source}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} (stored : StoredIdentity shape context environment before)
    (append : HeapAppends before after) : StoredIdentity shape context environment after := by
  rcases stored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
  exact ⟨definitionContext,captured,location,cell,lookup,append.read read,descriptor,fields⟩

theorem StoredIdentity.under {source : TypedSource} {shape : IdentityShape source}
    {context final : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (stored : StoredIdentity shape context environment heap) (next : TypedBinder)
    (location : Dynamic.Location) (different : next.id ≠ shape.binder.id)
    (extended : BinderExtends source.owner context next final) :
    StoredIdentity shape final ((next.id,location) :: environment) heap := by
  rcases stored with ⟨definitionContext,captured,found,cell,lookup,read,descriptor,fields⟩
  exact ⟨definitionContext,captured,found,cell,.tail different lookup,read,descriptor,
    fields.trans (.ofBinderExtends extended)⟩

theorem read_value {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Tests.SourceCoreNamedBranch.Read source binder type) {value : Dynamic.Value}
    (stored : StoredValue binder environment heap value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap read.node.id value heap := by
  rcases stored with ⟨location,cell,lookup,selected,ordinary,contents⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound read.found)
  · rw [read.form]
    exact .local (by rw [read.requirements,read.coercions]; rfl) lookup selected ordinary contents
  · rw [read.coercions]; exact .nil

theorem boolean_value {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Bool} (node : BooleanAt source value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id (.bool value) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .builtinBoolean (by rw [node.requirements,node.coercions]; rfl)
  · rw [node.coercions]; exact .nil

theorem call_typed {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type result : TypeSystem.Ty}
    (call : CallShape source binder argument type) {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context call.node.id result) :
    ∃ calleeType argumentType, ExpressionHasType source context call.callee.node.id calleeType ∧
      ExpressionHasType source context argument argumentType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans call.found)
    rw [call.form] at raw
    cases raw with
    | indirectCall callee arguments _ =>
      cases arguments with
      | cons argument _ => exact ⟨_,_,callee,argument⟩

theorem StoredIdentity.invoke {program : SourceSemantics.Program} {source : TypedSource}
    {shape : IdentityShape source} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before argumentsHeap : Dynamic.Heap}
    (stored : StoredIdentity shape context environment before)
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {argument : ExpressionId} {type result : TypeSystem.Ty} (call : CallShape source shape.binder argument type)
    (builtin : type = .word ∨ type = .bool)
    (typed : ExpressionHasType source context call.node.id result) {value : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument value argumentsHeap) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id value after ∧
      HeapAppends argumentsHeap after := by
  obtain ⟨calleeType, argumentType, callee, argumentTyped⟩ := call_typed call state.runtime.graph.nodeOccurrencesUnique typed
  obtain ⟨node,contains,sameType⟩ := callee.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete state.runtime.graph.nodeOccurrencesUnique contains).symm.trans call.callee.found)
  subst node
  have ground : TypeWellFormed context type := by
    rcases builtin with same | same
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .word⟩
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .bool⟩
  rcases stored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
  have descriptorTyped := ((state.heapTyped cell read.member).generalized_inv descriptor).2
  have argumentKept := wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped argumentTyped argumentTrace
  have readable : Readable argumentsHeap captured :=
    (Readable.of_agrees descriptorTyped.captures).mono argumentKept.heap_extends
  have trace := shape.invoke_from_typed call captured environment evidence state.runtime
    (by simpa only [state.runtime.signatures] using wellFormed.signatures)
    state.covers state.locals state.heapTyped (sameType.symm ▸ callee) ground lookup read descriptor fields argumentTrace
    (copies_spec_applySubstitution [(shape.typeVariable, type)] source readable)
  exact ⟨_,trace,(HeapAppends.of_copies source captured argumentsHeap).trans ⟨_,rfl⟩⟩


def valueHeap (before : Dynamic.Heap) (binder : TypedBinder) (value : Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := binder.scheme.body, value := some value}]⟩

/-- The generalized `let` copies the environment, then stores the principal
descriptor over the copies. -/
def identityHeap {source : TypedSource} (shape : IdentityShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source environment before).2.cells ++
    [{type := shape.binder.scheme.body, value := none,
      generalized := some (shape.descriptor context (copies source environment before).1)}]⟩

/-- The descriptor's location, after the copies of the environment. -/
def identityLocation (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    Dynamic.Location :=
  ⟨(copies source environment before).2.cells.length⟩

theorem identityHeap_appends {source : TypedSource} (shape : IdentityShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    HeapAppends before (identityHeap shape context environment before) :=
  (HeapAppends.of_copies source environment before).trans ⟨_,rfl⟩

theorem generalized_step {program : SourceSemantics.Program} {source : TypedSource}
    (shape : IdentityShape source) (site : StatementAt source (.letDecl shape.binder (some shape.lambda.id)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((shape.binder.id,identityLocation source environment before) :: environment))
      (identityHeap shape context environment before) ∧
    SourceState program source final evidence ((shape.binder.id,identityLocation source environment before) :: environment)
      (identityHeap shape context environment before) ∧
    StoredIdentity shape final ((shape.binder.id,identityLocation source environment before) :: environment)
      (identityHeap shape context environment before) ∧
    BinderExtends source.owner context shape.binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized _ mono _ => rw [shape.scheme] at mono; cases mono
  | letInitializedGeneralized polymorphic _ _ _ extended =>
    have snapshot := copies_spec source (Readable.of_agrees state.locals)
    have allocation : Dynamic.Heap.AllocatesGeneralized (copies source environment before).2
        (shape.descriptor context (copies source environment before).1)
        (identityLocation source environment before) (identityHeap shape context environment before) := .append
    have trace := Dynamic.StatementExecutes.letInitializedGeneralized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq snapshot
      (shape.captures context (copies source environment before).1) polymorphic extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,
      ⟨context,(copies source environment before).1,_,_,.head,allocation.reads_new,rfl,.ofBinderExtends extended⟩,
      extended⟩

theorem ordinary_step {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} {initializer : ExpressionId} (site : StatementAt source (.letDecl binder (some initializer)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before middle : Dynamic.Heap} {value : Dynamic.Value}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (mono : binder.scheme.quantified = []) {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts)
    (initializerTrace : Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((binder.id,⟨middle.cells.length⟩) :: environment)) (valueHeap middle binder value) ∧
    SourceState program source final evidence ((binder.id,⟨middle.cells.length⟩) :: environment) (valueHeap middle binder value) ∧
    StoredValue binder ((binder.id,⟨middle.cells.length⟩) :: environment) (valueHeap middle binder value) value ∧
    BinderExtends source.owner context binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitializedGeneralized impossible _ _ _ _ => exact (impossible mono).elim
  | letInitialized _ _ extended =>
    have allocation : Dynamic.Heap.Allocates middle binder.scheme.body (some value)
        ⟨middle.cells.length⟩ (valueHeap middle binder value) := .append
    have trace := Dynamic.StatementExecutes.letInitialized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq initializerTrace mono extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,⟨_,_,.head,allocation.reads_new,rfl,rfl⟩,extended⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalSource
/-! Exact original conditional occurrences retain both identity-call branches and
the following builtin value leaf in the original ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  trueNode : BooleanAt source true
  falseNode : BooleanAt source false
  yesCall : CallShape source f.binder trueNode.node.id .bool
  noCall : CallShape source f.binder falseNode.node.id .bool
  conditional : ExpressionNode
  conditionalFound : source.lookupExpression? conditional.id = some conditional
  conditionalForm : conditional.form = .conditional flagRead.node.id yesCall.node.id noCall.node.id
  conditionalRequirements : conditional.requirements = []
  conditionalCoercions : conditional.coercions = []
  builtin : ExpressionNode
  builtinName : String
  builtinFound : source.lookupExpression? builtin.id = some builtin
  builtinForm : builtin.form = .reference builtinName (.builtinFunction .wordToInteger)
  builtinRequirements : builtin.requirements = []
  builtinCoercions : builtin.coercions = []
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [conditional.id,builtin.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  fFlag : f.binder.id ≠ flag.id

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def boolean (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name (.builtinBoolean _) := node.form | throw (IO.userError "conditional original Boolean")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "conditional Boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "conditional Boolean value"
  let ⟨requirements⟩ ← observed (node.requirements = []) "conditional Boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "conditional Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "builtin original input")
  let [.expression parameterRead,.statement identityReturn,.expression lambda,.statement initialized,
       .expression flagNode,.expression trueExpr,.expression yesCallee,.expression yesExpr,
       .expression falseExpr,.expression noCallee,.expression noExpr,.expression conditional,
       .expression builtin,.expression tuple,.statement returned] := source.nodes | throw (IO.userError "builtin original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "builtin original declaration")
  let f ← identity source binder lambda parameterRead identityReturn
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let trueNode ← boolean source trueExpr true
  let falseNode ← boolean source falseExpr false
  let yesCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder trueNode.node.id .bool yesCallee yesExpr
  let noCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool noCallee noExpr
  let ⟨conditionalFound⟩ ← observed (source.lookupExpression? conditional.id = some conditional) "conditional identity"
  let ⟨conditionalForm⟩ ← observed (conditional.form = .conditional flagRead.node.id yesCall.node.id noCall.node.id) "conditional ordered branches"
  let ⟨conditionalRequirements⟩ ← observed (conditional.requirements = []) "conditional requirements"
  let ⟨conditionalCoercions⟩ ← observed (conditional.coercions = []) "conditional coercions"
  let .reference builtinName (.builtinFunction .wordToInteger) := builtin.form
    | throw (IO.userError "original builtin reference")
  let ⟨builtinFound⟩ ← observed (source.lookupExpression? builtin.id = some builtin) "builtin identity"
  let ⟨builtinForm⟩ ← observed (builtin.form = .reference builtinName (.builtinFunction .wordToInteger)) "builtin form"
  let ⟨builtinRequirements⟩ ← observed (builtin.requirements = []) "builtin requirements"
  let ⟨builtinCoercions⟩ ← observed (builtin.coercions = []) "builtin coercions"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [conditional.id,builtin.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "original inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "original roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "distinct identities"
  return ⟨flag,f,flagRead,trueNode,falseNode,yesCall,noCall,conditional,conditionalFound,conditionalForm,
    conditionalRequirements,conditionalCoercions,builtin,builtinName,builtinFound,builtinForm,builtinRequirements,builtinCoercions,
    ⟨initialized,initializedFound,initializedForm⟩,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,fFlag⟩

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalSourceFirst
/-! Construct the original declaration and conditional before target execution.
The test runs once, only its selected identity call runs, and the following
builtin leaf preserves that call’s actual heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem Shape.calls_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {result : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id result) :
    ∃ type, ExpressionHasType source context shape.yesCall.node.id type ∧
      ExpressionHasType source context shape.noCall.node.id type := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children =>
      cases children with
      | cons first _ =>
        cases first with
        | intro conditionalContains conditionalRaw _ _ _ _ =>
          cases Option.some.inj ((lookupExpression?_complete unique conditionalContains).symm.trans shape.conditionalFound)
          rw [shape.conditionalForm] at conditionalRaw
          cases conditionalRaw with
          | conditional _ yes no => exact ⟨_,yes,no⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after ∧ HeapAppends before after := by
  obtain ⟨middle, _, _, firstTyped, tailTyped⟩ := head_tail typed
  obtain ⟨declaration, stateNext, stored, _extended⟩ := generalized_step shape.f shape.initialized state wellFormed firstTyped
  obtain ⟨next, _, _, returnedTyped, _⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨type,yesTyped,noTyped⟩ := shape.calls_typed state.runtime.graph.nodeOccurrencesUnique tupleTyped
    have allocatedPrefix : HeapAppends before (identityHeap shape.f context environment before) :=
      identityHeap_appends shape.f context environment before
    have flagNext := (flagStored.mono allocatedPrefix).under (identityLocation source environment before) shape.fFlag
    have chosen : ∃ after, Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
        (identityHeap shape.f context environment before) shape.conditional.id (.bool flag) after ∧
        HeapAppends (identityHeap shape.f context environment before) after := by
      cases flag with
      | false =>
        obtain ⟨after, callTrace, append⟩ := stored.invoke stateNext wellFormed shape.noCall (.inr rfl)
          noTyped (boolean_value shape.falseNode)
        refine ⟨after,?_,append⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionalFound)
        · rw [shape.conditionalForm,shape.conditionalRequirements,shape.conditionalCoercions]
          exact .conditionalFalse rfl (read_value shape.flagRead flagNext) callTrace
        · rw [shape.conditionalCoercions]; exact .nil
      | true =>
        obtain ⟨after, callTrace, append⟩ := stored.invoke stateNext wellFormed shape.yesCall (.inr rfl)
          yesTyped (boolean_value shape.trueNode)
        refine ⟨after,?_,append⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionalFound)
        · rw [shape.conditionalForm,shape.conditionalRequirements,shape.conditionalCoercions]
          exact .conditionalTrue rfl (read_value shape.flagRead flagNext) callTrace
        · rw [shape.conditionalCoercions]; exact .nil
    obtain ⟨after, conditionalTrace, append⟩ := chosen
    have builtinTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment) after shape.builtin.id
        (.builtin ⟨.wordToInteger⟩) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.builtinFound)
      · rw [shape.builtinForm,shape.builtinRequirements,shape.builtinCoercions]
        exact .builtinFunction rfl
      · rw [shape.builtinCoercions]; exact .nil
    have tupleTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
        (identityHeap shape.f context environment before) shape.tuple.id
        (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
      · rw [shape.tupleForm,shape.tupleRequirements,shape.tupleCoercions]
        exact .tuple rfl (.cons conditionalTrace (.cons builtinTrace .nil)) (.cons (.singleton _))
      · rw [shape.tupleCoercions]; exact .nil
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans append⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMixedImperative (SourceState StoredValue)

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

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.node.id, shape.returned.node.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool)
    (heapTyped : Dynamic.HeapWellTyped selected.packet.header.function.context before) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final after, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)))
      after := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  have allocatedTyped := heapTyped.allocate (.some (.bool flag)) allocation
  have boundTyped : Dynamic.HeapWellTyped header.context (flagHeap before flag) :=
    allocatedTyped.transportClosed fields.signatures certified.runtime.closed runtime.closed
      certified.runtime.variables_closed runtime.residual_variables_open
  have state : SourceState (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      header.function.source header.context header.function.evidence
      (flagEnvironment shape.flag before) (flagHeap before flag) :=
    ⟨runtime, covers, locals, boundTyped⟩
  have stored : StoredValue shape.flag (flagEnvironment shape.flag before) (flagHeap before flag) (.bool flag) :=
    ⟨_, _, .head, allocation.reads_new, rfl, rfl⟩
  obtain ⟨next, after, body, _append⟩ := shape.body_from_source state wellFormed typed flag stored
  exact ⟨bound, next, after, selected.statements shape ▸ body⟩

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSourceBranch
/-! Both branches execute from independent Source states. The true branch
allocates its own generalized identity and ordinary result; the false branch
calls the outer identity. Each restores the incoming lexical environment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics

private theorem initializer_typed {source : TypedSource} {binder : TypedBinder} {initializer : ExpressionId}
    (site : StatementAt source (.letDecl binder (some initializer)))
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source) (mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context site.node.id final facts) :
    ExpressionHasType source context initializer binder.scheme.body := by
  have form := form_at unique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized value _ _ => exact value
  | letInitializedGeneralized impossible _ _ _ _ => exact (impossible mono).elim

/-- Actual Source execution is available for either original branch. -/
theorem Shape.branch_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementHasType source control context shape.branch.node.id final facts)
    (fStored : StoredIdentity shape.f context environment before)
    (firstStored : StoredValue shape.first environment before (.word (Word.ofNatModulo 11)))
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ after, Dynamic.StatementExecutes program context evidence source environment before shape.branch.node.id
      final (.fallthrough environment) after ∧ HeapAppends before after := by
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.branch.found typed
  rw [shape.branch.formEq] at original
  cases original with
  | ifWithElse conditionTyped thenTyped elseTyped =>
    have conditionTrace := read_value (program := program) (context := context) (evidence := evidence) shape.condition flagStored
    cases flag with
    | false =>
      obtain ⟨elseContext,_,_,discardTyped,_⟩ := head_tail elseTyped
      have discardForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.elseDiscard.found discardTyped
      rw [shape.elseDiscard.formEq] at discardForm
      cases discardForm with
      | expressionDiscard callTyped =>
        obtain ⟨after,callTrace,appended⟩ := fStored.invoke state wellFormed shape.elseCall (.inr rfl)
          callTyped (boolean_value shape.falseNode)
        have discarded := Dynamic.StatementExecutes.expression (lookupStatement?_sound shape.elseDiscard.found)
          shape.elseDiscard.formEq callTrace
        exact ⟨after,.ifFalseWithElse (lookupStatement?_sound shape.branch.found) shape.branch.formEq
          conditionTrace (.cons discarded .nil),appended⟩
    | true =>
      obtain ⟨gContext,_,_,gTyped,tailTyped⟩ := head_tail thenTyped
      obtain ⟨chosenContext,_,_,chosenTyped,discardTypedList⟩ := head_tail tailTyped
      obtain ⟨discardContext,_,_,discardTyped,_⟩ := head_tail discardTypedList
      obtain ⟨gTrace,gState,gStored,gExtended⟩ := generalized_step shape.g shape.gLet state wellFormed gTyped
      let gHeap := identityHeap shape.g context environment before
      have gAppended : HeapAppends before gHeap := identityHeap_appends shape.g context environment before
      have fAtG := (fStored.mono gAppended).under shape.g.binder (identityLocation source environment before) shape.gF gExtended
      have firstAtG := (firstStored.mono gAppended).under (identityLocation source environment before) shape.gFirst
      have chosenInitializer := initializer_typed shape.chosenLet state.runtime.graph.nodeOccurrencesUnique
        (by rw [shape.chosenScheme]; rfl) chosenTyped
      obtain ⟨middle,chosenCallTrace,chosenCallAppend⟩ := gStored.invoke gState wellFormed shape.chosenCall (.inl rfl)
        chosenInitializer (read_value shape.firstRead firstAtG)
      obtain ⟨chosenTrace,chosenState,chosenStored,chosenExtended⟩ := ordinary_step shape.chosenLet gState wellFormed
        (by rw [shape.chosenScheme]; rfl) chosenTyped chosenCallTrace
      let chosenHeap := valueHeap middle shape.chosen (.word (Word.ofNatModulo 11))
      have chosenAppend : HeapAppends middle chosenHeap := ⟨_,rfl⟩
      have fAtChosen := ((fAtG.mono chosenCallAppend).mono chosenAppend).under shape.chosen
        ⟨middle.cells.length⟩ shape.chosenF chosenExtended
      have discardForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.thenDiscard.found discardTyped
      rw [shape.thenDiscard.formEq] at discardForm
      cases discardForm with
      | expressionDiscard callTyped =>
        obtain ⟨after,callTrace,lastAppend⟩ := fAtChosen.invoke chosenState wellFormed shape.thenCall (.inl rfl)
          callTyped (read_value shape.chosenRead chosenStored)
        have discarded := Dynamic.StatementExecutes.expression (lookupStatement?_sound shape.thenDiscard.found)
          shape.thenDiscard.formEq callTrace
        have inner := Dynamic.StatementsExecute.cons gTrace (.cons chosenTrace (.cons discarded .nil))
        exact ⟨after,.ifTrue (lookupStatement?_sound shape.branch.found) shape.branch.formEq conditionTrace inner,
          gAppended.trans (chosenCallAppend.trans (chosenAppend.trans lastAppend))⟩

/-- The ordinary first declaration is evaluated before the original condition. -/
theorem Shape.block_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementHasType source control context shape.block.node.id final facts)
    (fStored : StoredIdentity shape.f context environment before)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ after, Dynamic.StatementExecutes program context evidence source environment before shape.block.node.id
      final (.fallthrough environment) after ∧ HeapAppends before after := by
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.block.found typed
  rw [shape.block.formEq] at original
  cases original with
  | block bodyTyped =>
    obtain ⟨firstContext,_,_,firstTyped,branchTypedList⟩ := head_tail bodyTyped
    obtain ⟨branchContext,_,_,branchTyped,_⟩ := head_tail branchTypedList
    have initializer := initializer_typed shape.firstLet state.runtime.graph.nodeOccurrencesUnique
      (by rw [shape.firstScheme]; rfl) firstTyped
    obtain ⟨_,_,_,literalTyped⟩ := call_typed shape.firstCall state.runtime.graph.nodeOccurrencesUnique initializer
    have literal := shape.eleven.evaluates (program := program) evidence environment before state.runtime.graph.nodeOccurrencesUnique literalTyped
    rw [shape.elevenValue] at literal
    obtain ⟨middle,firstCallTrace,firstCallAppend⟩ := fStored.invoke state wellFormed shape.firstCall (.inl rfl) initializer literal
    obtain ⟨firstTrace,firstState,firstStored,firstExtended⟩ := ordinary_step shape.firstLet state wellFormed
      (by rw [shape.firstScheme]; rfl) firstTyped firstCallTrace
    let firstHeap := valueHeap middle shape.first (.word (Word.ofNatModulo 11))
    have firstAppend : HeapAppends middle firstHeap := ⟨_,rfl⟩
    have fAtFirst := ((fStored.mono firstCallAppend).mono firstAppend).under shape.first
      ⟨middle.cells.length⟩ shape.firstF firstExtended
    have flagAtFirst := ((flagStored.mono firstCallAppend).mono firstAppend).under
      ⟨middle.cells.length⟩ shape.firstFlag
    obtain ⟨after,branchTrace,branchAppend⟩ := shape.branch_trace firstState wellFormed branchTyped fAtFirst
      firstStored flag flagAtFirst
    exact ⟨after,.block (lookupStatement?_sound shape.block.found) shape.block.formEq
      (.cons firstTrace (.cons branchTrace .nil)),firstCallAppend.trans (firstAppend.trans branchAppend)⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSourceFirst
/-! The complete original body is evaluated independently of native execution.
Both lexical exits restore the outer binding; the final two calls use the same
principal descriptor after the chosen branch has finished. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.finalWordCall.node.id left ∧
      ExpressionHasType source context shape.finalBoolCall.node.id right := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second _ => exact ⟨_,_,first,second⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : BodyFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.fLet.node.id,shape.block.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.block.node.id,shape.returned.node.id] finalContext
      (.returned (.product (.word (Word.ofNatModulo 17)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,rest⟩ := head_tail typed
  obtain ⟨blockContext,_,_,blockTyped,last⟩ := head_tail rest
  obtain ⟨returnContext,_,_,returnTyped,_⟩ := head_tail last
  obtain ⟨fTrace,fState,fStored,fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let firstHeap := identityHeap shape.f context environment before
  have firstAppend : HeapAppends before firstHeap := identityHeap_appends shape.f context environment before
  have flagAtF := (flagStored.mono firstAppend).under (identityLocation source environment before) shape.fFlag
  obtain ⟨blockHeap,blockTrace,blockAppend⟩ := shape.block_trace fState wellFormed blockTyped fStored flag flagAtF
  have blockForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.block.found blockTyped
  rw [shape.block.formEq] at blockForm
  cases blockForm with
  | block _ =>
    have blockState := fState.after_statement wellFormed blockTyped blockTrace
    have fAtBlock := fStored.mono blockAppend
    have flagAtBlock := flagAtF.mono blockAppend
    have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
    rw [shape.returned.formEq] at returnForm
    cases returnForm with
    | returnValue tupleTyped =>
      obtain ⟨_,_,wordTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
      obtain ⟨_,_,_,literalTyped⟩ := call_typed shape.finalWordCall state.runtime.graph.nodeOccurrencesUnique wordTyped
      have literal := shape.seventeen.evaluates (program := program) evidence ((shape.f.binder.id,(identityLocation source environment before)) :: environment) blockHeap
        state.runtime.graph.nodeOccurrencesUnique literalTyped
      rw [shape.seventeenValue] at literal
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtBlock.invoke blockState wellFormed shape.finalWordCall
        (.inl rfl) wordTyped literal
      have wordState := blockState.after_expression wellFormed wordTyped wordTrace
      have fAtWord := fAtBlock.mono wordAppend
      have flagAtWord := flagAtBlock.mono wordAppend
      obtain ⟨after,boolTrace,boolAppend⟩ := fAtWord.invoke wordState wellFormed shape.finalBoolCall
        (.inr rfl) boolTyped (read_value shape.flagRead flagAtWord)
      have tupleTrace : Dynamic.ExpressionEvaluates program fContext evidence source
          ((shape.f.binder.id,(identityLocation source environment before)) :: environment) blockHeap shape.tuple.id
          (.product (.word (Word.ofNatModulo 17)) (.bool flag)) after := by
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
        · rw [shape.tupleForm]
          exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
            (.cons wordTrace (.cons boolTrace .nil)) (.cons (.singleton _))
        · rw [shape.tupleCoercions]; exact .nil
      have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
        shape.returned.formEq tupleTrace
      refine ⟨fContext,after,.cons fTrace (.cons blockTrace ?_),firstAppend.trans (blockAppend.trans (wordAppend.trans boolAppend))⟩
      apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
      · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
      · exact returned

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
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

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.fLet.node.id, shape.block.node.id, shape.returned.node.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool)
    (heapTyped : Dynamic.HeapWellTyped selected.packet.header.function.context before) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final after, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.word (Word.ofNatModulo 17)) (.bool flag)))
      after := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  have allocatedTyped := heapTyped.allocate (.some (.bool flag)) allocation
  have boundTyped : Dynamic.HeapWellTyped header.context (flagHeap before flag) :=
    allocatedTyped.transportClosed fields.signatures certified.runtime.closed runtime.closed
      certified.runtime.variables_closed runtime.residual_variables_open
  have state : SourceState (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      header.function.source header.context header.function.evidence
      (flagEnvironment shape.flag before) (flagHeap before flag) :=
    ⟨runtime, covers, locals, boundTyped⟩
  have stored : StoredValue shape.flag (flagEnvironment shape.flag before) (flagHeap before flag) (.bool flag) :=
    ⟨_, _, .head, allocation.reads_new, rfl, rfl⟩
  obtain ⟨next, after, body, _append⟩ := shape.body_from_source state wellFormed typed flag stored
  exact ⟨bound, next, after, selected.statements shape ▸ body⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeTyping
/-! A bounded observer constructs declarative typing for the complete original
mixed body, including branches, lexical scopes, loops and mapping writes. It accepts
only the expression and statement forms used by this regression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
namespace OriginalValidation
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

private def observe := @Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
private def localFacts : StatementFacts :=
  ⟨.unit, false, false, .ordinary .unit⟩

private def parameters (owner : Resolved.DeclarationId) (context : SourceSemantics.Context) :
    (values : List TypedBinder) → IO ((final : SourceSemantics.Context) ×
      PLift (MonoBindersExtend owner context values (values.map (·.scheme.body)) final))
  | [] => pure ⟨context, ⟨.nil _⟩⟩
  | value :: rest => do
    let ⟨mono⟩ ← observe (value.scheme = .mono value.scheme.body) "mixed parameter scheme"
    let ⟨extended⟩ ← binder context owner value
    let ⟨final,⟨tail⟩⟩ ← parameters owner
      (context.withLocal value.id value.scheme value.schemeRequirements) rest
    return ⟨final, ⟨.cons mono extended tail⟩⟩

private def reference {source : TypedSource} (context : SourceSemantics.Context)
    (node : ExpressionNode) (found : source.lookupExpression? node.id = some node)
    (name : String) (id : Resolved.LocalId)
    (form : node.form = .reference name (.local id)) :
    IO (PLift (ExpressionHasType source context node.id node.type)) := do
  match schemeFound : Resolved.LocalScope.lookup? context.locals id with
  | none => throw (IO.userError "mixed local scheme lookup")
  | some schemeValue =>
    let ⟨requirements⟩ ← observe (Resolved.LocalScope.lookup? context.localSchemeRequirements id = some [])
      "mixed unqualified lexical reference"
    let value : TypedBinder := {id, name, scheme := schemeValue}
    let ⟨raw⟩ ← observe (node.rawType = node.type) "mixed local raw type"
    let ⟨empty⟩ ← observe (node.requirements = []) "mixed local requirements"
    let ⟨coercions⟩ ← observe (node.coercions = []) "mixed local coercions"
    let shape : Tests.SourceCoreNamedBranch.Read source value node.type := {
      node := node, found := found, form := form, raw := raw,
      type := rfl, requirements := empty, coercions := coercions }
    read shape context (Resolved.LocalScope.lookup?_iff.mp schemeFound)
      (Resolved.LocalScope.lookup?_iff.mp requirements)

private def writable (context : SourceSemantics.Context) (id : Resolved.LocalId) (type : TypeSystem.Ty) :
    IO (PLift (WritableLocal context id type)) := do
  match found : Resolved.LocalScope.lookup? context.locals id with
  | none => throw (IO.userError "mixed assignment root")
  | some actual =>
    let ⟨formed⟩ ← scheme context actual
    let ⟨mono⟩ ← observe (actual.quantified = []) "mixed writable monomorphic root"
    let ⟨same⟩ ← observe (actual.body = type) "mixed writable root type"
    return ⟨.intro (Resolved.LocalScope.lookup?_iff.mp found) formed mono same⟩

private def compound : (operator : Syntax.ValueAssignOp) → IO (PLift (WordCompoundAssignmentOperator operator))
  | .equal => throw (IO.userError "mixed compound operator")
  | .add => pure ⟨.add⟩
  | .subtract => pure ⟨.subtract⟩
  | .multiply => pure ⟨.multiply⟩
  | .divide => pure ⟨.divide⟩
  | .modulo => pure ⟨.modulo⟩
  | .bitAnd => pure ⟨.bitAnd⟩
  | .bitXor => pure ⟨.bitXor⟩
  | .bitOr => pure ⟨.bitOr⟩
  | .shiftLeft => pure ⟨.shiftLeft⟩
  | .shiftRight => pure ⟨.shiftRight⟩
  | .uncheckedAdd => pure ⟨.uncheckedAdd⟩
  | .uncheckedSubtract => pure ⟨.uncheckedSubtract⟩
  | .uncheckedMultiply => pure ⟨.uncheckedMultiply⟩

structure Statement (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (id : StatementId) where
  final : SourceSemantics.Context
  facts : StatementFacts
  typed : StatementHasType source control context id final facts

structure Statements (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (ids : List StatementId) where
  final : SourceSemantics.Context
  facts : BodyFacts
  typed : StatementsHaveType source control context ids final facts

mutual
  def expression : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (id : ExpressionId) → (expected : TypeSystem.Ty) → IO (PLift (ExpressionHasType source context id expected))
    | 0, _, _, _, _ => throw (IO.userError "mixed typing expression bound")
    | fuel + 1, source, context, id, expected => do
      match found : source.lookupExpression? id with
      | none => throw (IO.userError "mixed original expression")
      | some node =>
        let ⟨same⟩ ← observe (node.id = id) "mixed original expression identity"
        let foundAt : source.lookupExpression? node.id = some node := same ▸ found
        let ⟨result⟩ ← observe (node.type = expected) "mixed expression result type"
        let ⟨typed⟩ ← (show IO (PLift (ExpressionHasType source context node.id node.type)) from do
          match form : node.form with
          | .reference name (.local localId) => reference context node foundAt name localId form
          | .reference _ (.builtinBoolean value) =>
            let ⟨typed⟩ ← uncoerced context node .bool foundAt (form ▸ .reference (.builtinBoolean value))
            let ⟨typeEq⟩ ← observe (node.type = .bool) "mixed Boolean type"
            return ⟨typeEq.symm ▸ typed⟩
          | .reference _ (.builtinFunction function) =>
            let ⟨typed⟩ ← uncoerced context node function.type foundAt (form ▸ .reference (.builtinFunction function))
            let ⟨typeEq⟩ ← observe (node.type = function.type) "mixed builtin function type"
            return ⟨typeEq.symm ▸ typed⟩
          | .integerLiteral literal resolution =>
            let ⟨target⟩ ← observe (resolution.targetType = .word) "mixed integer target"
            let ⟨requirements⟩ ← observe (node.requirements = [resolution.requirement]) "mixed integer requirements"
            let ⟨coercions⟩ ← observe (node.coercions = []) "mixed integer coercions"
            let ⟨typeEq⟩ ← observe (node.type = .word) "mixed integer type"
            let ⟨typed⟩ ← word ⟨node,literal,resolution,foundAt,form,target,requirements,coercions⟩ context
            return ⟨typeEq.symm ▸ typed⟩
          | .unary .logicalNot operand =>
            let ⟨child⟩ ← expression fuel source context operand .bool
            let ⟨typeEq⟩ ← observe (node.type = .bool) "mixed logical not result"
            let ⟨typed⟩ ← uncoerced context node .bool foundAt
              (form ▸ .unary child .logicalNot)
            return ⟨typeEq.symm ▸ typed⟩
          | .binary left .logicalAnd right =>
            let ⟨leftTyped⟩ ← expression fuel source context left .bool
            let ⟨rightTyped⟩ ← expression fuel source context right .bool
            let ⟨typeEq⟩ ← observe (node.type = .bool) "mixed logical and result"
            let ⟨typed⟩ ← uncoerced context node .bool foundAt
              (form ▸ .binary leftTyped rightTyped .booleanAnd)
            return ⟨typeEq.symm ▸ typed⟩
          | .index base key =>
            let some baseNode := source.lookupExpression? base | throw (IO.userError "mixed index base")
            let .mapping keyType _ := baseNode.type | throw (IO.userError "mixed index mapping type")
            let ⟨baseTyped⟩ ← expression fuel source context base (.mapping keyType node.type)
            let ⟨keyTyped⟩ ← expression fuel source context key keyType
            uncoerced context node node.type foundAt (form ▸ .index baseTyped keyTyped)
          | .group inner =>
            let ⟨child⟩ ← expression fuel source context inner node.type
            uncoerced context node node.type foundAt (form ▸ .group child)
          | .conditional test yes no =>
            let ⟨testTyped⟩ ← expression fuel source context test .bool
            let ⟨yesTyped⟩ ← expression fuel source context yes node.type
            let ⟨noTyped⟩ ← expression fuel source context no node.type
            uncoerced context node node.type foundAt
              (form ▸ .conditional testTyped yesTyped noTyped)
          | .tuple children =>
            let ⟨types,⟨childrenTyped⟩⟩ ← expressions fuel source context children
            let ⟨typeEq⟩ ← observe (node.type = TypeSystem.Ty.productMany types) "mixed tuple type"
            let ⟨typed⟩ ← uncoerced context node (TypeSystem.Ty.productMany types) foundAt (form ▸ .tuple childrenTyped)
            return ⟨typeEq.symm ▸ typed⟩
          | .call callee arguments (.indirect metadata) =>
            let ⟨types,⟨argumentsTyped⟩⟩ ← expressions fuel source context arguments
            let ⟨calleeTyped⟩ ← expression fuel source context callee
              (.function metadata.argumentTypeAfterCoercion node.type)
            let ⟨arity⟩ ← observe (metadata.argumentCount = types.length) "mixed call arity"
            let ⟨before⟩ ← observe (metadata.argumentTypeBeforeCoercion = TypeSystem.Ty.productMany types) "mixed call input"
            let ⟨after⟩ ← observe (metadata.argumentTypeAfterCoercion = TypeSystem.Ty.productMany types) "mixed call output"
            let ⟨argumentCoercions⟩ ← observe (metadata.argumentCoercions = []) "mixed call argument coercions"
            let ⟨raw⟩ ← observe (node.rawType = node.type) "mixed call raw type"
            let ⟨requirements⟩ ← observe (node.requirements = []) "mixed call requirements"
            let ⟨coercions⟩ ← observe (node.coercions = []) "mixed call coercions"
            let ⟨formed⟩ ← admissible context node.type
            have application : IndirectApplicationValid context metadata types metadata.argumentTypeAfterCoercion :=
              .intro arity before rfl (by rw [before,after,argumentCoercions]; exact .nil _)
            return ⟨.intro (lookupExpression?_sound foundAt)
              (form ▸ ExpressionFormHasRawType.indirectCall calleeTyped argumentsTyped application) raw formed formed (by
                rw [requirements,coercions,argumentCoercions]
                exact .indirectCall (by intro step member; cases member) (.nil _) rfl)⟩
          | .lambda values resultType body =>
            let ⟨unique⟩ ← observe ((values.map (·.name)).Nodup) "mixed lambda names"
            let ⟨lambdaContext,⟨extended⟩⟩ ← parameters source.owner context values
            let bodyTyped ← statements fuel source {returnType := resultType} lambdaContext body
            let ⟨completes⟩ ← observe (bodyTyped.facts.control.mayBreak = false ∧
              bodyTyped.facts.control.mayContinue = false ∧
              ((bodyTyped.facts.control.fallthrough = none ∧ bodyTyped.facts.control.mayReturn = true) ∨
                bodyTyped.facts.control.fallthrough = some resultType)) "mixed lambda completion"
            let type := TypeSystem.Ty.function (TypeSystem.Ty.productMany (values.map (·.scheme.body))) resultType
            let ⟨typeEq⟩ ← observe (node.type = type) "mixed lambda type"
            let ⟨typed⟩ ← uncoerced context node type foundAt
              (form ▸ .lambda unique extended bodyTyped.typed completes)
            return ⟨typeEq.symm ▸ typed⟩
          | _ => throw (IO.userError "unsupported original mixed expression"))
        return ⟨by simpa only [same,result] using typed⟩

  def expressions : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (ids : List ExpressionId) → IO ((types : List TypeSystem.Ty) × PLift (ExpressionsHaveTypes source context ids types))
    | 0, _, _, _ => throw (IO.userError "mixed typing expression sequence bound")
    | _ + 1, _, context, [] => pure ⟨[],⟨.nil context⟩⟩
    | fuel + 1, source, context, id :: rest => do
      let some node := source.lookupExpression? id | throw (IO.userError "mixed sequence original expression")
      let ⟨head⟩ ← expression fuel source context id node.type
      let ⟨types,⟨tail⟩⟩ ← expressions fuel source context rest
      return ⟨node.type :: types,⟨.cons head tail⟩⟩

  def projections : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (root : TypeSystem.Ty) → (steps : List PlaceProjection) → (leaf : TypeSystem.Ty) →
      IO (PLift (SourceProjectionsHaveType source context root steps leaf))
    | 0, _, _, _, _, _ => throw (IO.userError "mixed projection typing bound")
    | _ + 1, _, _, root, [], leaf => do
      let ⟨same⟩ ← observe (root = leaf) "mixed projection leaf type"
      return ⟨by cases same; exact .nil root⟩
    | fuel + 1, source, context, .mapping keyType valueType, .index key :: rest, leaf => do
      let ⟨keyTyped⟩ ← expression fuel source context key keyType
      let ⟨restTyped⟩ ← projections fuel source context valueType rest leaf
      return ⟨.index keyTyped restTyped⟩
    | _ + 1, _, _, _, _, _ => throw (IO.userError "unsupported mixed place projection")

  def place : (fuel : Nat) → (source : TypedSource) → (context : SourceSemantics.Context) →
      (target : PlaceResolution) → IO (PLift (SourcePlaceHasType source context target target.type))
    | 0, _, _, _ => throw (IO.userError "mixed place typing bound")
    | fuel + 1, source, context, target => do
      let some root := Resolved.LocalScope.lookup? context.locals target.root
        | throw (IO.userError "mixed place root declaration")
      let ⟨rootTyped⟩ ← writable context target.root root.body
      let ⟨stepsTyped⟩ ← projections fuel source context root.body target.projections target.type
      return ⟨.intro rootTyped stepsTyped rfl⟩

  def statement : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (id : StatementId) → IO (Statement source control context id)
    | 0, _, _, _, _ => throw (IO.userError "mixed typing statement bound")
    | fuel + 1, source, control, context, id => do
      match found : source.lookupStatement? id with
      | none => throw (IO.userError "mixed original statement")
      | some node =>
        match form : node.form with
        | .letDecl value none =>
          let ⟨mono⟩ ← observe (value.scheme.quantified = []) "mixed absent monomorphic binder"
          let ⟨extended⟩ ← binder context source.owner value
          let final := context.withLocal value.id value.scheme value.schemeRequirements
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed absent declaration type"
          match accepted : validateSchemeGeneralizes context value.scheme with
          | .error _ => throw (IO.userError "mixed absent generalization")
          | .ok () => return ⟨final,localFacts,.letUninitialized (lookupStatement?_sound found) form mono
              (validateSchemeGeneralizes_success accepted) extended typeEq⟩
        | .letDecl value (some initializer) =>
          let ⟨extended⟩ ← binder context source.owner value
          let final := context.withLocal value.id value.scheme value.schemeRequirements
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed declaration type"
          if mono : value.scheme.quantified = [] then
            let ⟨typed⟩ ← expression fuel source context initializer value.scheme.body
            match accepted : validateSchemeGeneralizes context value.scheme with
            | .error _ => throw (IO.userError "mixed ordinary generalization")
            | .ok () => return ⟨final,localFacts,.letInitialized (lookupStatement?_sound found) form typed mono
                (validateSchemeGeneralizes_success accepted) extended typeEq⟩
          else
            let ⟨requirements⟩ ← observe (value.schemeRequirements = []) "mixed generalized requirements"
            let ⟨generalized⟩ ← generalizes context value
            let ⟨typed⟩ ← expression fuel source (localSchemeInitializerContext context value) initializer value.scheme.body
            return ⟨final,localFacts,.letInitializedGeneralized (lookupStatement?_sound found) form mono
              (LocalSchemeRequirementsWellFormed.empty _ _ requirements) generalized typed extended typeEq⟩
        | .returnStmt (some value) =>
          let ⟨typed⟩ ← expression fuel source context value control.returnType
          let ⟨typeEq⟩ ← observe (node.type = control.returnType) "mixed return type"
          return ⟨context,⟨control.returnType,true,true,.returned⟩,
            .returnValue (lookupStatement?_sound found) form typed typeEq⟩
        | .expression value true =>
          let some child := source.lookupExpression? value | throw (IO.userError "mixed discarded expression")
          let ⟨typed⟩ ← expression fuel source context value child.type
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed discard type"
          return ⟨context,localFacts,.expressionDiscard (lookupStatement?_sound found) form typed typeEq⟩
        | .forLoop initial condition post body =>
          let ⟨loopContext,⟨initialTyped⟩⟩ ← forItems fuel source control context initial
          let ⟨conditionTyped⟩ ← expression fuel source loopContext condition .bool
          let bodyTyped ← statements fuel source control.enterLoop loopContext body
          let ⟨_,⟨postTyped⟩⟩ ← forItems fuel source control.enterLoop loopContext post
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed for type"
          return ⟨context,⟨.unit,false,false,.loop bodyTyped.facts.control⟩,
            .forLoop (lookupStatement?_sound found) form initialTyped conditionTyped bodyTyped.typed postTyped typeEq⟩
        | .whileLoop condition body =>
          let ⟨conditionTyped⟩ ← expression fuel source context condition .bool
          let bodyTyped ← statements fuel source control.enterLoop context body
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed while type"
          return ⟨context,⟨.unit,false,false,.loop bodyTyped.facts.control⟩,
            .whileLoop (lookupStatement?_sound found) form conditionTyped bodyTyped.typed typeEq⟩
        | .assignValue assignment operator rhs =>
          let ⟨targetTyped⟩ ← place fuel source context assignment.target
          let ⟨rhsTyped⟩ ← expression fuel source context rhs assignment.target.type
          let ⟨requirements⟩ ← observe (assignment.requirements = []) "mixed assignment requirements"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed assignment statement type"
          let ⟨assignmentTyped⟩ ← (show IO (PLift (SourceAssignmentHasType source context assignment operator rhs)) from do
            if equal : operator = .equal then
              return ⟨equal.symm ▸ .equal targetTyped rhsTyped requirements⟩
            else
              let ⟨kind⟩ ← compound operator
              let ⟨word⟩ ← observe (assignment.target.type = .word) "mixed compound Word target"
              return ⟨.wordCompound kind (word ▸ targetTyped) (word ▸ rhsTyped) requirements⟩)
          return ⟨context,localFacts,.assignValue (lookupStatement?_sound found) form assignmentTyped typeEq⟩
        | .breakStmt =>
          let ⟨allowed⟩ ← observe (0 < control.loopDepth) "mixed break inside loop"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed break type"
          return ⟨context,⟨.unit,false,false,.breaking⟩,.breakStmt (lookupStatement?_sound found) form allowed typeEq⟩
        | .continueStmt =>
          let ⟨allowed⟩ ← observe (0 < control.loopDepth) "mixed continue inside loop"
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed continue type"
          return ⟨context,⟨.unit,false,false,.continuing⟩,.continueStmt (lookupStatement?_sound found) form allowed typeEq⟩
        | .block body =>
          let child ← statements fuel source control context body
          let ⟨typeEq⟩ ← observe (node.type = child.facts.type) "mixed block type"
          return ⟨context,⟨child.facts.type,child.facts.sawReturn,child.facts.sawReturn,child.facts.control.eraseValue⟩,
            .block (lookupStatement?_sound found) form child.typed typeEq⟩
        | .ifThen condition yes none =>
          let ⟨conditionTyped⟩ ← expression fuel source context condition .bool
          let yesTyped ← statements fuel source control context yes
          let ⟨typeEq⟩ ← observe (node.type = .unit) "mixed branch without else type"
          return ⟨context,⟨.unit,false,false,yesTyped.facts.control.branches (.ordinary .unit)⟩,
            .ifWithoutElse (lookupStatement?_sound found) form conditionTyped yesTyped.typed typeEq⟩
        | .ifThen condition yes (some no) =>
          let ⟨conditionTyped⟩ ← expression fuel source context condition .bool
          let yesTyped ← statements fuel source control context yes
          let noTyped ← statements fuel source control context no
          let returns := yesTyped.facts.sawReturn && noTyped.facts.sawReturn
          let type := if returns then control.returnType else .unit
          let ⟨typeEq⟩ ← observe (node.type = type) "mixed branch type"
          return ⟨context,⟨type,returns,returns,yesTyped.facts.control.branches noTyped.facts.control⟩,
            .ifWithElse (lookupStatement?_sound found) form conditionTyped yesTyped.typed noTyped.typed typeEq⟩
        | _ => throw (IO.userError "unsupported original mixed statement")

  def forItems : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (items : List ForItemForm) →
      IO ((final : SourceSemantics.Context) × PLift (ForItemsHaveType source control context items final))
    | 0, _, _, _, _ => throw (IO.userError "mixed typing for header bound")
    | _ + 1, _, control, context, [] => pure ⟨context,⟨.nil control context⟩⟩
    | fuel + 1, source, control, context, item :: rest => do
      let ⟨middle,⟨head⟩⟩ ← (show IO ((middle : SourceSemantics.Context) ×
          PLift (ForItemHasType source control context item middle)) from do
        match itemEq : item with
        | .letDecl value initializer =>
          let ⟨mono⟩ ← observe (value.scheme.quantified = []) "mixed for ordinary binder"
          let ⟨extended⟩ ← binder context source.owner value
          let final := context.withLocal value.id value.scheme value.schemeRequirements
          match accepted : validateSchemeGeneralizes context value.scheme with
          | .error _ => throw (IO.userError "mixed for ordinary generalization")
          | .ok () =>
            let generalized := validateSchemeGeneralizes_success accepted
            match initialEq : initializer with
            | none => return ⟨final,⟨by rw [itemEq,initialEq]; exact .letUninitialized mono generalized extended⟩⟩
            | some id =>
              let ⟨typed⟩ ← expression fuel source context id value.scheme.body
              return ⟨final,⟨by rw [itemEq,initialEq]; exact .letInitialized typed mono generalized extended⟩⟩
        | .expression id =>
          let some node := source.lookupExpression? id | throw (IO.userError "mixed for expression")
          let ⟨typed⟩ ← expression fuel source context id node.type
          return ⟨context,⟨itemEq.symm ▸ .expression typed⟩⟩
        | .assignValue assignment operator rhs =>
          let ⟨targetTyped⟩ ← place fuel source context assignment.target
          let ⟨rhsTyped⟩ ← expression fuel source context rhs assignment.target.type
          let ⟨requirements⟩ ← observe (assignment.requirements = []) "mixed for assignment requirements"
          let ⟨assignmentTyped⟩ ← (show IO (PLift (SourceAssignmentHasType source context assignment operator rhs)) from do
            if equal : operator = .equal then
              return ⟨equal.symm ▸ .equal targetTyped rhsTyped requirements⟩
            else
              let ⟨kind⟩ ← compound operator
              let ⟨word⟩ ← observe (assignment.target.type = .word) "mixed for compound Word target"
              return ⟨.wordCompound kind (word ▸ targetTyped) (word ▸ rhsTyped) requirements⟩)
          return ⟨context,⟨itemEq.symm ▸ .assignValue assignmentTyped⟩⟩
        | .assignBitNot _ => throw (IO.userError "unsupported original mixed for unary assignment"))
      let ⟨final,⟨tail⟩⟩ ← forItems fuel source control middle rest
      return ⟨final,⟨.cons head tail⟩⟩

  def statements : (fuel : Nat) → (source : TypedSource) → (control : ControlContext) →
      (context : SourceSemantics.Context) → (ids : List StatementId) → IO (Statements source control context ids)
    | 0, _, _, _, _ => throw (IO.userError "mixed typing statement sequence bound")
    | _ + 1, _, control, context, [] => pure ⟨context,.empty,.nil control context⟩
    | fuel + 1, source, control, context, [id] => do
      let head ← statement fuel source control context id
      return ⟨head.final,.singleton head.facts,.singleton head.typed⟩
    | fuel + 1, source, control, context, id :: next :: rest => do
      let head ← statement fuel source control context id
      let tail ← statements fuel source control head.final (next :: rest)
      return ⟨tail.final,.cons head.facts tail.facts,.cons head.typed tail.typed⟩
end
end OriginalValidation

abbrev BodyTyping := Tests.SourceCoreGeneralizedExport.BodyTyping

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let base := checkedBodyContext signatures signature function
  let ⟨context,⟨inputs⟩⟩ ← OriginalValidation.parameters signature.id base function.typedBody.inputs
  let ⟨inputTypes⟩ ← observed (function.typedBody.inputs.map (·.scheme.body) = signature.parameterTypes) "mixed original input types"
  let roots ← function.typedBody.roots.mapM fun root => match root with
    | .statement id => pure id
    | .expression _ => throw (IO.userError "mixed original statement roots")
  let ⟨rootsEq⟩ ← observed (function.typedBody.roots = roots.map NodeId.statement) "mixed original complete roots"
  let result := TypeSystem.Ty.productMany signature.returnTypes
  let body ← OriginalValidation.statements 1000 function.typedBody {returnType := result} context roots
  let ⟨typeEq⟩ ← observed (body.facts.type = result) "mixed original whole body type"
  return ⟨roots,rootsEq,result,body.facts,typeEq,context,body.final,inputTypes ▸ inputs,body.typed,rfl⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalTyping
/-! The builtin-value regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "mixed conditional full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed conditional original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "mixed conditional original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed conditional original complete cache size")
  IO.println "MIXED_CONDITIONAL_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_CONDITIONAL_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
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
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
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

structure SourceTrace (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (before : Dynamic.Heap) (flag : Bool) where
  finalContext : SourceSemantics.Context
  after : Dynamic.Heap
  allocated : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
  trace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
    selected.packet.header.function.body finalContext
    (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  source : SourceTrace selected shape ⟨[]⟩ flag
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag initial.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  source : SourceTrace selected shape retained.state.heap flag
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag ready.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedConditional
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_retained
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session []) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.first_success _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    exact ⟨⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

/-- Each actual later success keeps the previous handles and captured cells,
using the independently reconstructed Source execution at the prior heap. -/
theorem NextForward.observed_retained (next : NextForward first retained flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session entries) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control next.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) next.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller next.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      next.ready.history.physical next.ready.stable next.ready.heapTyped next.ready.argumentsTyped issued bodySelected
      next.ready.represented next.ready.history.semantic.current.2.1 rfl next.start.started next.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.after_success _ _ next.start.selected next.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry next.ready.contextAt)
        retained.exportsReady next.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        next.ready.history
    exact ⟨⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := next.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result next.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedConditional
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedConditionalRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "conditionalPair"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      let .product (.bool true) (.function _) := firstReturned.value
        | throw (IO.userError "builtin returned value shape")
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        let .product (.bool false) (.function _) := secondReturned.value
          | throw (IO.userError "builtin returned value shape")
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          let .product (.bool true) (.function _) := thirdReturned.value
            | throw (IO.userError "builtin returned value shape")
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,17,32,47]) "mixed conditional Source-certified repeated native heaps changed"
          IO.println "MIXED_CONDITIONAL_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_CONDITIONAL_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_CONDITIONAL_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed conditional certified call did not succeed")
      | _ => throw (IO.userError "second mixed conditional certified call did not succeed")
    | _ => throw (IO.userError "first mixed conditional certified call did not succeed")
  else throw (IO.userError "mixed conditional callable catalog disabled")

end Tests.SourceCoreMixedConditional.ObservedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "mixed imperative full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed imperative original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "mixed imperative original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed imperative original complete cache size")
  IO.println "MIXED_IMPERATIVE_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_IMPERATIVE_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativePublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
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
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativePublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
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

structure SourceTrace (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (before : Dynamic.Heap) (flag : Bool) where
  finalContext : SourceSemantics.Context
  after : Dynamic.Heap
  allocated : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
  trace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
    selected.packet.header.function.body finalContext
    (.returned (.product (.word (Word.ofNatModulo 17)) (.bool flag))) after

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  source : SourceTrace selected shape ⟨[]⟩ flag
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.word (Word.ofNatModulo 17)) (.bool flag))
    source.after

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag initial.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicImperativeNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  source : SourceTrace selected shape retained.state.heap flag
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.word (Word.ofNatModulo 17)) (.bool flag))
    source.after

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag ready.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicImperativeNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_retained
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session []) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.first_success _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    exact ⟨⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

/-- Each actual later success keeps the previous handles and captured cells,
using the independently reconstructed Source execution at the prior heap. -/
theorem NextForward.observed_retained (next : NextForward first retained flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session entries) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control next.source.trace)
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) next.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller next.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      next.ready.history.physical next.ready.stable next.ready.heapTyped next.ready.argumentsTyped issued bodySelected
      next.ready.represented next.ready.history.semantic.current.2.1 rfl next.start.started next.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.after_success _ _ next.start.selected next.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry next.ready.contextAt)
        retained.exportsReady next.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        next.ready.history
    exact ⟨⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := next.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result next.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedImperative
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedImperativeRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "mixed"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      require (firstReturned.value == .product (.word (Word.ofNatModulo 17)) (.bool true))
        "first mixed imperative retained Source value changed"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == .product (.word (Word.ofNatModulo 17)) (.bool false))
          "second mixed imperative retained Source value changed"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == .product (.word (Word.ofNatModulo 17)) (.bool true))
            "third mixed imperative retained Source value changed"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,59,95,152]) "mixed imperative Source-certified repeated native heaps changed"
          IO.println "MIXED_IMPERATIVE_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_IMPERATIVE_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_IMPERATIVE_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed imperative certified call did not succeed")
      | _ => throw (IO.userError "second mixed imperative certified call did not succeed")
    | _ => throw (IO.userError "first mixed imperative certified call did not succeed")
  else throw (IO.userError "mixed imperative callable catalog disabled")

end Tests.SourceCoreMixedImperative.ObservedRuntime
end
