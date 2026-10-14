import Solcore.Test.SourceCoreSelectedCompletionSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

inductive Example where
  | branch (flag : Bool)
  | tail
  | unit
  | letUnit
  deriving DecidableEq, Repr

def Example.workspace (spec : Example) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    match spec with
    | .branch _ => "function choose(flag: Bool, value: Word) returns (Word) { if (flag) { let copy: Word = value; return copy; } else { return value; } }"
    | .tail => "function identity(value: Word) returns (Word) { value }"
    | .unit => "function empty() {}"
    | .letUnit => "function consume(value: Word) { let copy: Word = value; }"}] }

def Example.Shape (spec : Example) (function : CheckedFunction) (signature : ProgramFunctionSignature) : Type :=
  match spec with
  | .branch _ => Tests.SourceCoreNamedBranch.FactoryShape function signature
  | .tail => TailShape function.typedBody
  | .unit => PLift (UnitShape function.typedBody)
  | .letUnit => LetUnitShape function.typedBody

def Example.resultType : Example → TypeSystem.Ty
  | .branch _ | .tail => .word
  | .unit | .letUnit => .unit

def Example.arguments : Example → List SourceCorePublicValues.Value
  | .branch flag => [.bool flag, .word (Word.ofNatModulo 37)]
  | .tail | .letUnit => [.word (Word.ofNatModulo 37)]
  | .unit => []

def Example.values : Example → List Dynamic.Value
  | .branch flag => [.bool flag, .word (Word.ofNatModulo 37)]
  | .tail | .letUnit => [.word (Word.ofNatModulo 37)]
  | .unit => []

def Example.result : Example → Dynamic.Value
  | .branch _ | .tail => .word (Word.ofNatModulo 37)
  | .unit | .letUnit => .unit

def Example.heap : Example → Dynamic.Heap
  | .branch flag => branchHeap flag (Word.ofNatModulo 37)
  | .tail => tailHeap (Word.ofNatModulo 37)
  | .unit => ⟨[]⟩
  | .letUnit => letUnitHeap (Word.ofNatModulo 37)

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def observeShape (spec : Example) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (spec.Shape function signature) := by
  cases spec with
  | branch flag => exact Tests.SourceCoreNamedBranch.observeShape function signature
  | tail => exact do
    match inputs : function.typedBody.inputs with
    | [binder] =>
      match roots : function.typedBody.roots with
      | [.statement id] =>
        let some statement := function.typedBody.lookupStatement? id
          | throw (IO.userError "completion tail statement")
        match form : statement.form with
        | .expression expression false =>
          let some node := function.typedBody.lookupExpression? expression
            | throw (IO.userError "completion tail read")
          let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder node .word
          let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "completion tail scheme"
          let ⟨found⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "completion tail lookup"
          let ⟨rootEq⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "completion tail root"
          let ⟨formEq⟩ ← observed (statement.form = .expression read.node.id false) "completion tail form"
          return ⟨binder, read, statement, inputs, binderScheme, rootEq, found, formEq⟩
        | _ => throw (IO.userError "completion tail expression form")
      | _ => throw (IO.userError "completion tail roots")
    | _ => throw (IO.userError "completion tail inputs")
  | unit => exact do
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = []) "completion unit inputs"
    let ⟨roots⟩ ← observed (function.typedBody.roots = []) "completion unit roots"
    return ⟨⟨inputs, roots⟩⟩
  | letUnit => exact do
    match inputs : function.typedBody.inputs with
    | [argument] =>
      match roots : function.typedBody.roots with
      | [.statement id] =>
        let some statement := function.typedBody.lookupStatement? id
          | throw (IO.userError "completion Unit local statement")
        match form : statement.form with
        | .letDecl binder (some expression) =>
          let some node := function.typedBody.lookupExpression? expression
            | throw (IO.userError "completion Unit local initializer")
          let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument node .word
          let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "completion Unit argument scheme"
          let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "completion Unit local scheme"
          let ⟨found⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "completion Unit local lookup"
          let ⟨rootEq⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "completion Unit local root"
          let ⟨formEq⟩ ← observed (statement.form = .letDecl binder (some read.node.id)) "completion Unit local form"
          return ⟨argument, binder, read, statement, inputs, argumentScheme, binderScheme, rootEq, found, formEq⟩
        | _ => throw (IO.userError "completion Unit local form")
      | _ => throw (IO.userError "completion Unit local roots")
    | _ => throw (IO.userError "completion Unit local inputs")

structure Fixture (spec : Example) where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram spec.workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  signature : ProgramFunctionSignature
  shape : spec.Shape named.specialized.function signature
  resultType : named.specialized.function.inferredBodyType = spec.resultType
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture (spec : Example) : IO (Fixture spec) := do
  match checked : checkProgram spec.workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "completion artifact absent")
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
            have original : checkProgram spec.workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "completion selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "completion original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let [signature] := recipe.compiled.sourceProgram.signatures.functions
                  | throw (IO.userError "completion original signature")
                let shape ← observeShape spec named.specialized.function signature
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = spec.resultType) "completion function result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "completion substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "completion function marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "completion parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "completion physical slot"
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
                  signature := signature
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "completion cache shape")

theorem Fixture.eligible {spec : Example} (fixture : Fixture spec) :
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

structure Started {spec : Example} (fixture : Fixture spec) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key spec.arguments runOptions

def observeStarted {spec : Example} (fixture : Fixture spec) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "completion bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key spec.arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedCompletion
