import Solcore.Test.SourceCoreSelectedProjectedBitNotProgram
import Solcore.Test.SourceCoreSelectedProjectedBitNotSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

/-- Named/header proof entries are configured before compilation. The original
checked program still contains the captured factory, whose proof profile is a
separate recorded boundary. -/
def namedHeaderEntries : List String := [
  "key", "failedKey", "invert", "nested", "effects", "keyFailure",
  "calledKeyFailure", "nestedFailure", "initialize", "post", "stop", "defaultLocal"]

private def compileEntries (entries : Option (List String)) : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let selected := match entries with
      | none => program.signatures.functions
      | some names => program.signatures.functions.filter (fun signature => names.contains signature.name)
    let seeds := selected.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "projected artifact absent")
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


/-- Complete compiler/runtime companion: every original declaration is a seed. -/
def compileFixture : IO CompiledFixture := compileEntries none

/-- Actual selected compiler receipt for all twelve named/header entries. -/
def compileNamedHeaderFixture : IO CompiledFixture := compileEntries (some namedHeaderEntries)

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
    | throw (IO.userError "projected original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "projected original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "projected global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "projected substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "projected ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "projected ordinary parameters"
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
    | _ => throw (IO.userError "projected unique physical slot")

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
  let .statement sid := id | throw (IO.userError "projected statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "projected statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "projected read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeUnary (source : TypedSource) : IO (UnaryShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .assignBitNot resolution := assigned.form | throw (IO.userError "projected assignment form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  return ⟨table, key, resolution, assigned, returned, keyRead, result, inputs,
    tableScheme, keyScheme, keyTable, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "missing inputs")
  let [first, second, third] := source.roots | throw (IO.userError "missing roots")
  let declared ← statement source first
  let assigned ← statement source second
  let returned ← statement source third
  let .letDecl absent none := declared.form | throw (IO.userError "missing declaration")
  let .assignBitNot resolution := assigned.form | throw (IO.userError "missing assignment")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "missing index")
  let absentRead ← wordRead source absent keyId
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "missing original inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "missing table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "missing key scheme"
  let ⟨absentScheme⟩ ← observed (absent.scheme = .mono .word) "missing absent scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "missing distinct key"
  let ⟨absentTable⟩ ← observed (absent.id ≠ table.id) "missing distinct absent/table"
  let ⟨absentKey⟩ ← observed (absent.id ≠ key.id) "missing distinct absent/key"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assigned.id, .statement returned.id]) "missing original roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl absent none) "missing declaration form"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "missing assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "missing assignment form"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "missing target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index absentRead.node.id]) "missing key identity"
  return ⟨table, key, absent, resolution, declared, assigned, returned, absentRead, inputs,
    tableScheme, keyScheme, absentScheme, keyTable, absentTable, absentKey, roots,
    declaredFound, declaredForm, assignedFound, assignedForm, targetRoot, targetProjections⟩

def observeCopy (source : TypedSource) : IO (CopyShape source) := do
  let [argument] := source.inputs | throw (IO.userError "copy inputs")
  let [first, second] := source.roots | throw (IO.userError "copy roots")
  let initialized ← statement source first
  let returned ← statement source second
  let .letDecl copy (some initializerId) := initialized.form | throw (IO.userError "copy initialized local")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "copy return")
  let initializer ← wordRead source argument initializerId
  let result ← wordRead source copy resultId
  let ⟨inputs⟩ ← observed (source.inputs = [argument]) "copy original inputs"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "copy argument scheme"
  let ⟨copyScheme⟩ ← observed (copy.scheme = .mono .word) "copy local scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement returned.id]) "copy original roots"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "copy initialized identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl copy (some initializer.node.id)) "copy initialized form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "copy returned identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "copy returned form"
  return ⟨argument, copy, initialized, returned, initializer, result, inputs, argumentScheme,
    copyScheme, roots, initializedFound, initializedForm, returnedFound, returnedForm⟩

def observeInitializer (source : TypedSource) : IO (InitializerShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .forLoop [.assignBitNot resolution] conditionId post [] := assigned.form | throw (IO.userError "projected initializer form")
  let some condition := source.lookupExpression? conditionId | throw (IO.userError "projected initializer condition")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .forLoop [.assignBitNot resolution] condition.id post []) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "initializer condition identity"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference "false" (.builtinBoolean false)) "initializer false condition"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "initializer condition requirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "initializer condition coercions"
  return ⟨table, key, resolution, condition, post, assigned, returned, keyRead, result, inputs,
    tableScheme, keyScheme, keyTable, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm, conditionFound, conditionForm, conditionRequirements, conditionCoercions⟩

private def expression (source : TypedSource) (id : ExpressionId) : IO ExpressionNode := do
  let some node := source.lookupExpression? id | throw (IO.userError "nested expression lookup")
  return node

private def observeIndex (source : TypedSource) (node : ExpressionNode) (base key : ExpressionId) :
    IO (IndexRead source base key) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "nested index identity"
  let ⟨form⟩ ← observed (node.form = .index base key) "nested index form"
  let ⟨requirements⟩ ← observed (node.requirements = []) "nested index requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "nested index coercions"
  return ⟨node, found, form, requirements, coercions⟩

def observeNested (source : TypedSource) : IO (NestedShape source) := do
  let [table, first, second] := source.inputs | throw (IO.userError "nested original inputs")
  let [a, b] := source.roots | throw (IO.userError "nested original roots")
  let assigned ← statement source a
  let returned ← statement source b
  let .assignBitNot resolution := assigned.form | throw (IO.userError "nested assignment")
  let [.index firstId, .index secondId] := resolution.target.projections | throw (IO.userError "nested target indices")
  let firstRead ← wordRead source first firstId
  let secondRead ← wordRead source second secondId
  let .returnStmt (some returnedId) := returned.form | throw (IO.userError "nested return")
  let outerNode ← expression source returnedId
  let .index innerId secondReturnId := outerNode.form | throw (IO.userError "nested outer return index")
  let innerNode ← expression source innerId
  let .index baseId firstReturnId := innerNode.form | throw (IO.userError "nested inner return index")
  let baseNode ← expression source baseId
  let baseRead ← Tests.SourceCoreNamedBranch.observeRead source table baseNode nestedType
  let returnFirst ← wordRead source first firstReturnId
  let returnSecond ← wordRead source second secondReturnId
  let inner ← observeIndex source innerNode baseRead.node.id returnFirst.node.id
  let outer ← observeIndex source outerNode inner.node.id returnSecond.node.id
  let ⟨inputs⟩ ← observed (source.inputs = [table, first, second]) "nested inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono nestedType) "nested tableScheme"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono .word) "nested firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono .word) "nested secondScheme"
  let ⟨firstTable⟩ ← observed (first.id ≠ table.id) "nested firstTable"
  let ⟨secondTable⟩ ← observed (second.id ≠ table.id) "nested secondTable"
  let ⟨secondFirst⟩ ← observed (second.id ≠ first.id) "nested secondFirst"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "nested roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "nested assignedFound"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "nested assignedForm"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "nested targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index firstRead.node.id, .index secondRead.node.id]) "nested targetProjections"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "nested returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some outer.node.id)) "nested returnedForm"
  return ⟨table, first, second, resolution, assigned, returned, firstRead, secondRead,
    baseRead, returnFirst, returnSecond, inner, outer, inputs, tableScheme, firstScheme, secondScheme, firstTable, secondTable, secondFirst, roots, assignedFound, assignedForm, targetRoot, targetProjections, returnedFound, returnedForm⟩

structure ObservedProgram (fixture : CompiledFixture) where
  nestedRow : Row fixture
  initializerRow : Row fixture
  nestedShape : NestedShape nestedRow.original.function.typedBody
  initializerShape : InitializerShape initializerRow.original.function.typedBody
  keyRow : Row fixture
  invertRow : Row fixture
  missingRow : Row fixture
  keyShape : CopyShape keyRow.original.function.typedBody
  invertShape : UnaryShape invertRow.original.function.typedBody
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 12
  originals : fixture.recipe.compiled.sourceProgram.signatures.functions.length = 13

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let nestedRow ← observeRow fixture "nested"
  let initializerRow ← observeRow fixture "initialize"
  let nestedShape ← observeNested nestedRow.original.function.typedBody
  let initializerShape ← observeInitializer initializerRow.original.function.typedBody
  let keyRow ← observeRow fixture "key"
  let invertRow ← observeRow fixture "invert"
  let missingRow ← observeRow fixture "keyFailure"
  let keyShape ← observeCopy keyRow.original.function.typedBody
  let invertShape ← observeUnary invertRow.original.function.typedBody
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 12) "projected unary named/header selected cache"
  let ⟨originals⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.functions.length = 13) "projected unary complete original program"
  return ⟨nestedRow, initializerRow, nestedShape, initializerShape, keyRow, invertRow, missingRow, keyShape, invertShape, missingShape, cacheSize, originals⟩

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
  | .outOfFuel _ => throw (IO.userError "projected bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedProjectedBitNot
