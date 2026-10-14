import Solcore.Test.SourceCoreSelectedCompoundSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function add(left: Word, right: Word) returns (Word) { left += right; return left; } function divide(left: Word, right: Word) returns (Word) { left /= right; return left; } function missing(right: Word) returns (Word) { let value: Word; value /= right; return value; }"}] }
def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  nativeResult : global.resultType = .word
  resultType : original.function.inferredBodyType = .word
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "compound artifact absent")
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

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "compound original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "compound original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "compound global key"
      let ⟨nativeResult⟩ ← observed (global.resultType = .word) "compound native result"
      let ⟨resultType⟩ ← observed (original.function.inferredBodyType = .word) "compound raw result"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "compound substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "compound ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "compound ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        nativeResult := nativeResult
        resultType := resultType
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "compound unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

private def statement (source : TypedSource) (id : NodeId) : IO StatementNode := do
  let .statement sid := id | throw (IO.userError "compound statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "compound statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "compound read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeCompound (source : TypedSource) (operation : Operation) : IO (CompoundShape source operation) := do
  let [left, right] := source.inputs | throw (IO.userError "compound parameter count")
  let [first, second] := source.roots | throw (IO.userError "compound statement count")
  let assignment ← statement source first
  let returned ← statement source second
  let .assignValue resolution _ rhsId := assignment.form | throw (IO.userError "compound assignment form")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "compound return form")
  let rhs ← wordRead source right rhsId
  let result ← wordRead source left resultId
  let ⟨inputs⟩ ← observed (source.inputs = [left, right]) "compound original inputs"
  let ⟨leftScheme⟩ ← observed (left.scheme = .mono .word) "compound left scheme"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "compound right scheme"
  let ⟨distinct⟩ ← observed (right.id ≠ left.id) "compound binder identity"
  let ⟨roots⟩ ← observed (source.roots = [.statement assignment.id, .statement returned.id]) "compound original roots"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "compound assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution operation.operator rhs.node.id) "compound original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = left.id) "compound target identity"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "compound bare target"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "compound return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "compound return read"
  return ⟨left, right, resolution, assignment, returned, rhs, result, inputs, leftScheme, rightScheme,
    distinct, roots, assignmentFound, assignmentForm, targetRoot, targetBare, returnedFound, returnedForm⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [right] := source.inputs | throw (IO.userError "missing parameter count")
  let [first, second, third] := source.roots | throw (IO.userError "missing statement count")
  let declared ← statement source first
  let assignment ← statement source second
  let returned ← statement source third
  let .letDecl binder none := declared.form | throw (IO.userError "missing local declaration")
  let .assignValue resolution .divide rhsId := assignment.form | throw (IO.userError "missing division assignment")
  let rhs ← wordRead source right rhsId
  let ⟨inputs⟩ ← observed (source.inputs = [right]) "missing inputs"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "missing input scheme"
  let ⟨localScheme⟩ ← observed (binder.scheme = .mono .word) "missing local scheme"
  let ⟨distinct⟩ ← observed (binder.id ≠ right.id) "missing distinct binders"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]) "missing roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl binder none) "missing absent declaration"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "missing assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .divide rhs.node.id) "missing operator identity"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "missing target root"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "missing target projections"
  return ⟨right, binder, resolution, declared, assignment, returned, rhs, inputs, rightScheme, localScheme,
    distinct, roots, declaredFound, declaredForm, assignmentFound, assignmentForm, targetRoot, targetBare⟩

structure ObservedProgram (fixture : CompiledFixture) where
  addRow : Row fixture
  divideRow : Row fixture
  missingRow : Row fixture
  addShape : CompoundShape addRow.original.function.typedBody .add
  divideShape : CompoundShape divideRow.original.function.typedBody .divide
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 3

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let addRow ← observeRow fixture "add"
  let divideRow ← observeRow fixture "divide"
  let missingRow ← observeRow fixture "missing"
  let addShape ← observeCompound addRow.original.function.typedBody .add
  let divideShape ← observeCompound divideRow.original.function.typedBody .divide
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 3) "compound cache size"
  return ⟨addRow, divideRow, missingRow, addShape, divideShape, missingShape, cacheSize⟩

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
  | .outOfFuel _ => throw (IO.userError "compound bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedCompound
