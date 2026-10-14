import Solcore.Test.SourceCoreSelectedLoopSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function stop(value: Word) returns (Word) { for (let copy: Word = value; true; ) { break; } return value; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "loop control source input shape")
  let [.expression first, .expression condition, .statement breaking, .statement loop, .expression second, .statement returned] := source.nodes
    | throw (IO.userError s!"loop control occurrence shape: {reprStr source.nodes}")
  let .forLoop [.letDecl copy (some _)] _ [] [_] := loop.form
    | throw (IO.userError "loop control header shape")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "loop control inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "loop control binderType"
  let ⟨copyType⟩ ← observed (copy.scheme = .mono .word) "loop control copyType"
  let ⟨roots⟩ ← observed (source.roots = [.statement loop.id, .statement returned.id]) "loop control roots"
  let ⟨firstFound⟩ ← observed (source.lookupExpression? first.id = some first) "loop control firstFound"
  let ⟨firstForm⟩ ← observed (first.form = .reference binder.name (.local binder.id)) "loop control firstForm"
  let ⟨firstRequirements⟩ ← observed (first.requirements = []) "loop control firstRequirements"
  let ⟨firstCoercions⟩ ← observed (first.coercions = []) "loop control firstCoercions"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "loop control conditionFound"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference "true" (.builtinBoolean true)) "loop control conditionForm"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "loop control conditionRequirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "loop control conditionCoercions"
  let ⟨breakingFound⟩ ← observed (source.lookupStatement? breaking.id = some breaking) "loop control breakingFound"
  let ⟨breakingForm⟩ ← observed (breaking.form = .breakStmt) "loop control breakingForm"
  let ⟨loopFound⟩ ← observed (source.lookupStatement? loop.id = some loop) "loop control loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl copy (some first.id)] condition.id [] [breaking.id]) "loop control loopForm"
  let ⟨secondFound⟩ ← observed (source.lookupExpression? second.id = some second) "loop control secondFound"
  let ⟨secondForm⟩ ← observed (second.form = .reference binder.name (.local binder.id)) "loop control secondForm"
  let ⟨secondRequirements⟩ ← observed (second.requirements = []) "loop control secondRequirements"
  let ⟨secondCoercions⟩ ← observed (second.coercions = []) "loop control secondCoercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "loop control returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some second.id)) "loop control returnedForm"
  return {
    binder := binder
    copy := copy
    first := first
    condition := condition
    breaking := breaking
    loop := loop
    second := second
    returned := returned
    inputs := inputs
    binderType := binderType
    copyType := copyType
    roots := roots
    firstFound := firstFound
    firstForm := firstForm
    firstRequirements := firstRequirements
    firstCoercions := firstCoercions
    conditionFound := conditionFound
    conditionForm := conditionForm
    conditionRequirements := conditionRequirements
    conditionCoercions := conditionCoercions
    breakingFound := breakingFound
    breakingForm := breakingForm
    loopFound := loopFound
    loopForm := loopForm
    secondFound := secondFound
    secondForm := secondForm
    secondRequirements := secondRequirements
    secondCoercions := secondCoercions
    returnedFound := returnedFound
    returnedForm := returnedForm }

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  shape : Shape named.specialized.function.typedBody
  resultType : named.specialized.function.inferredBodyType = .word
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "loop control artifact absent")
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
            have original : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "loop control selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "loop control original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .word) "loop control factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "loop control substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "loop control factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "loop control parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "loop control physical slot"
                return {
                  recipe := recipe
                  checked := original
                  seeds := seeds
                  facade := publicCompiled
                  accepted := accepted
                  selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade
                  profile := profile
                  original := originalRow
                  originalMember := by
                    rw [originals]
                    exact List.mem_cons_self
                  named := named
                  functions := functions
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "loop control cache shape")

theorem Fixture.eligible (fixture : Fixture) :
    Nonempty (SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted
    fixture.selected fixture.originalMember
  have member := List.mem_of_getElem? prepared.selected
  rw [fixture.functions] at member
  have same := List.mem_singleton.mp member
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram fixture.named.specialized := by
    rw [← same, prepared.same]
    exact prepared.origin
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      fixture.named.specialized.parameterSubstitution := by
    rw [fixture.substitution]
    intro parameter replacement impossible
    cases impossible
  exact ⟨⟨fixture.named, 0, fixture.named.signature,
    by rw [fixture.functions]; rfl, fixture.slot, rfl,
    ⟨origin, range, fixture.ordinary, fixture.ordinaryInputs⟩⟩⟩

structure Started (fixture : Fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key [.word seed] runOptions

def observeStarted (fixture : Fixture) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "loop control bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedLoop
