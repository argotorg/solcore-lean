import Solcore.Test.SourceCoreSelectedCapturedDirectSourceFirst
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "captured source input shape")
  let [.expression read, .statement inner, .expression lambda, .statement outer] := source.nodes
    | throw (IO.userError "captured source occurrence shape")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "captured inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "captured parameter type"
  let ⟨roots⟩ ← observed (source.roots = [.statement outer.id]) "captured roots"
  let ⟨readFound⟩ ← observed (source.lookupExpression? read.id = some read) "captured read occurrence"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured read form"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured read requirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured read coercions"
  let ⟨innerFound⟩ ← observed (source.lookupStatement? inner.id = some inner) "captured inner occurrence"
  let ⟨innerForm⟩ ← observed (inner.form = .returnStmt (some read.id)) "captured inner return"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "captured lambda occurrence"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [] .word [inner.id]) "captured lambda"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "captured lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "captured lambda coercions"
  let ⟨outerFound⟩ ← observed (source.lookupStatement? outer.id = some outer) "captured outer occurrence"
  let ⟨outerForm⟩ ← observed (outer.form = .returnStmt (some lambda.id)) "captured outer return"
  return {
    binder := binder
    read := read
    inner := inner
    lambda := lambda
    outer := outer
    inputs := inputs
    binderType := binderType
    roots := roots
    readFound := readFound
    readForm := readForm
    readRequirements := readRequirements
    readCoercions := readCoercions
    innerFound := innerFound
    innerForm := innerForm
    lambdaFound := lambdaFound
    lambdaForm := lambdaForm
    lambdaRequirements := lambdaRequirements
    lambdaCoercions := lambdaCoercions
    outerFound := outerFound
    outerForm := outerForm }

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
  resultType : named.specialized.function.inferredBodyType = .function .unit .word
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
      | none => throw (IO.userError "captured artifact absent")
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
              | throw (IO.userError "captured selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "captured original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .function .unit .word) "captured factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "captured substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "captured factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "captured parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "captured physical slot"
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
              | _ => throw (IO.userError "captured cache shape")

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
  | .outOfFuel _ => throw (IO.userError "captured bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

theorem from_source (fixture : Fixture) (started : Started fixture) :
    ∃ (issued : Profiled fixture.recipe) (initial : Initial issued.toIssued started.call)
      (shape : Shape initial.header.function.source),
      ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
        (.closure (capturedFunction initial.header shape)) (capturedHeap seed) ∧
        (ForwardChain issued seed started.call initial shape invocation ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]) ∧
        ((SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
            (.value (.closure (capturedFunction initial.header shape))) (capturedHeap seed) ∧
          SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
            issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint
            (.closure (capturedFunction initial.header shape)) (capturedHeap seed)) ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans (congrArg (fun named => named.specialized.function.typedBody)
    (namedEq.trans rowSame))
  let shape : Shape initial.header.function.source := sourceEq.symm ▸ fixture.shape
  have resultType : initial.header.function.resultType = .function .unit .word := by
    rw [initial.header.agreement.result, namedEq, rowSame]
    exact fixture.resultType
  refine ⟨issued, initial, shape, ?_⟩
  intro invocation
  have first := initial_source_first issued seed started.call initial shape resultType invocation
  exact ⟨first.1, first.2, initial_whole_output issued seed started.call initial shape invocation⟩

end Tests.SourceCoreSelectedCapturedDirect
