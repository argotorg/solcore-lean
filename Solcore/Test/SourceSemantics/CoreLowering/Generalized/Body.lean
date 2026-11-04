import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Control
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput

/-!
# Generalized body tests

Generalized bodies: body expressions and lexical bodies.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionProbe
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function duplicate(flag: Bool) returns (((Word, Word), (Bool, Word)), ((Bool, Bool), (Bool, Word))) {",
    "  let f = lam(value) { return ((value, value), (flag, 0)); };",
    "  return (f(11), f(flag));",
    "}" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}
def publicOutput (flag : Bool) : SourceCorePublicValues.Value :=
  .product (.product (.product (.word (word 11)) (.word (word 11))) (.product (.bool flag) (.word (word 0))))
    (.product (.product (.bool flag) (.bool flag)) (.product (.bool flag) (.word (word 0))))

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | _ => throw (IO.userError s!"{label}: public execution did not succeed")

def nativeProbe : IO Unit := do
  let program ← get "check duplicate" (checkProgram workspace options.checkingFuel)
  let source ← get "compile duplicate" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "complete cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete original/cache"
  let recipe ← get "prepare duplicate" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "root absent")
  let facade ← get "public duplicate" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "true" (← initial.run root.key [.bool true] runOptions)
  require (first.value == publicOutput true) "first duplicate/captured/numeric value"
  let second ← succeeded "false" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == publicOutput false) "second duplicate/captured/numeric value"
  let third ← succeeded "true again" (← second.session.run root.key [.bool true] runOptions)
  require (third.value == publicOutput true) "third duplicate/captured/numeric value"
  IO.println s!"GENERALIZED_BODY_EXPRESSION_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,third.session.heapSize]}"
  IO.println "GENERALIZED_BODY_EXPRESSION_NATIVE_PASS"
end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
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
      | none => throw (IO.userError "generalized body expression artifact absent")
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
    | throw (IO.userError "generalized body expression original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized body expression original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized body expression global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized body expression substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized body expression ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized body expression ordinary parameters"
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
    | _ => throw (IO.userError "generalized body expression unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "generalized body expression complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "generalized body expression complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "generalized body expression complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "duplicate"
  IO.println "GENERALIZED_BODY_EXPRESSION_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
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

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionSource
/-! The complete original lambda keeps both parameter reads, its captured Bool,
and its numeric leaf. Observations record syntax and typing metadata only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read observeRead)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StatementAt)

def resultType (type : TypeSystem.Ty) : TypeSystem.Ty := .product (.product type type) (.product .bool .word)
def resultValue (value : Dynamic.Value) (flag : Bool) : Dynamic.Value :=
  .product (.product value value) (.product (.bool flag) (.word (Word.ofNatModulo 0)))
def outputValue (flag : Bool) : Dynamic.Value :=
  .product (resultValue (.word (Word.ofNatModulo 11)) flag) (resultValue (.bool flag) flag)

structure PairAt (source : TypedSource) (left right : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .tuple [left,right]
  requirements : node.requirements = []
  coercions : node.coercions = []

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Read source binder (.function type (resultType type))
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure LambdaShape (source : TypedSource) where
  binder : TypedBinder
  parameter : TypedBinder
  flag : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  lambda : ExpressionNode
  returned : StatementNode
  first : Read source parameter (.variable typeVariable)
  second : Read source parameter (.variable typeVariable)
  duplicate : PairAt source first.node.id second.node.id
  capture : Read source flag .bool
  zero : WordNode source
  extra : PairAt source capture.node.id zero.node.id
  result : PairAt source duplicate.node.id extra.node.id
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (resultType (.variable typeVariable))⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (resultType (.variable typeVariable)) [returned.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  returnFound : source.lookupStatement? returned.id = some returned
  returnForm : returned.form = .returnStmt (some result.node.id)
  zeroValue : zero.resolution.rawValue = 0
  parameterFlag : parameter.id ≠ flag.id

structure Shape (source : TypedSource) where
  f : LambdaShape source
  literal : WordNode source
  flagRead : Read source f.flag .bool
  wordCall : CallShape source f.binder literal.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : PairAt source wordCall.node.id boolCall.node.id
  returned : StatementAt source (.returnStmt (some tuple.node.id))
  inputs : source.inputs = [f.flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : f.flag.scheme = .mono .bool
  literalValue : literal.resolution.rawValue = 11
  fFlag : f.binder.id ≠ f.flag.id
abbrev Shape.flag {source : TypedSource} (shape : Shape source) := shape.f.flag

private def pair (source : TypedSource) (left right : ExpressionId) (node : ExpressionNode) : IO (PairAt source left right) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "pair occurrence"
  let ⟨form⟩ ← observed (node.form = .tuple [left,right]) "pair ordered children"
  let ⟨requirements⟩ ← observed (node.requirements = []) "pair requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "pair coercions"
  return ⟨node,found,form,requirements,coercions⟩

private def call (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId) (type : TypeSystem.Ty)
    (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← observeRead source binder callee (.function type (resultType type))
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "call occurrence"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "call ordered argument"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "call arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "call argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩


def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "original input")
  let [.expression first,.expression second,.expression duplicate,.expression capture,.expression zero,
      .expression extra,.expression result,.statement lambdaReturn,.expression lambda,.statement initialized,
      .expression literal,.expression wordCallee,.expression wordCall,.expression flagRead,
      .expression boolCallee,.expression boolCall,.expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "complete original duplicate graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "original generalized binder")
  let .lambda [parameter] _ _ := lambda.form | throw (IO.userError "original lambda")
  let .variable typeVar := parameter.scheme.body | throw (IO.userError "principal parameter")
  let first ← observeRead source parameter first (.variable typeVar)
  let second ← observeRead source parameter second (.variable typeVar)
  let duplicate ← pair source first.node.id second.node.id duplicate
  let capture ← observeRead source flag capture .bool
  let zero ← wordNode source zero
  let extra ← pair source capture.node.id zero.node.id extra
  let result ← pair source duplicate.node.id extra.node.id result
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (resultType (.variable typeVar))⟩) "principal duplicate scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "parameter scheme"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "parameter requirements"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "lambda occurrence"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (resultType (.variable typeVar)) [lambdaReturn.id]) "lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "lambda raw"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "lambda type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? lambdaReturn.id = some lambdaReturn) "lambda return occurrence"
  let ⟨returnForm⟩ ← observed (lambdaReturn.form = .returnStmt (some result.node.id)) "lambda return expression"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "numeric leaf zero"
  let ⟨parameterFlag⟩ ← observed (parameter.id ≠ flag.id) "captured binder differs"
  let f : LambdaShape source := ⟨binder,parameter,flag,typeVar,lambda,lambdaReturn,first,second,duplicate,capture,zero,extra,result,
    scheme,requirements,parameterScheme,parameterRequirements,lambdaFound,lambdaForm,lambdaRaw,lambdaType,
    lambdaRequirements,lambdaCoercions,returnFound,returnForm,zeroValue,parameterFlag⟩
  let literal ← wordNode source literal
  let flagRead ← observeRead source flag flagRead .bool
  let wordCall ← call source binder literal.node.id .word wordCallee wordCall
  let boolCall ← call source binder flagRead.node.id .bool boolCallee boolCall
  let tuple ← pair source wordCall.node.id boolCall.node.id tuple
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration occurrence"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return occurrence"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.node.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [f.flag]) "complete original parameters"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "complete original roots"
  let ⟨flagScheme⟩ ← observed (f.flag.scheme = .mono .bool) "flag scheme"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "argument literal"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ f.flag.id) "capture distinct from declaration"
  return ⟨f,literal,flagRead,wordCall,boolCall,⟨initialized,initializedFound,initializedForm⟩,tuple,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,literalValue,fFlag⟩

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionCalls
/-! Source evaluation is built from the original lambda, the call's copy of
its actual captured cell and the instantiated static frame. No Core run
supplies a body trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StoredValue)
open Tests.SourceSemanticsCaptureCopies (copy_reads)

 theorem PairAt.children {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context pair.node.id type) :
    ∃ leftType rightType, ExpressionHasType source context left leftType ∧ ExpressionHasType source context right rightType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans pair.found)
    rw [pair.form] at raw
    cases raw with
    | tuple children => cases children with | cons first tail => cases tail with | cons second _ => exact ⟨_,_,first,second⟩

theorem PairAt.evaluates {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {first second : Dynamic.Value}
    (a : Dynamic.ExpressionEvaluates program context evidence source environment before left first middle)
    (b : Dynamic.ExpressionEvaluates program context evidence source environment middle right second after) :
    Dynamic.ExpressionEvaluates program context evidence source environment before pair.node.id (.product first second) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound pair.found)
  · rw [pair.form,pair.requirements,pair.coercions]
    exact .tuple rfl (.cons a (.cons b .nil)) (.cons (.singleton _))
  · rw [pair.coercions]; exact .nil

def PairAt.substitute {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) (substitution : TypeSystem.Substitution) :
    PairAt (source.applySubstitution substitution) left right := {
  node := pair.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ pair.found
  form := by simp [ExpressionNode.applySubstitution,pair.form,ExpressionForm.applySubstitution]
  requirements := by simp [ExpressionNode.applySubstitution,pair.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,pair.coercions] }

def substituteRead {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Read source binder type) (substitution : TypeSystem.Substitution) :
    Read (source.applySubstitution substitution) (binder.applySubstitution substitution) (substitution.apply type) := {
  node := read.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ read.found
  form := by simp [ExpressionNode.applySubstitution,read.form,ExpressionForm.applySubstitution,TypedBinder.applySubstitution,ReferenceResolution.applySubstitution]
  raw := by simp [ExpressionNode.rawType,ExpressionNode.applySubstitution,read.coercions,read.type]
  type := by simp [ExpressionNode.applySubstitution,read.type]
  requirements := by simp [ExpressionNode.applySubstitution,read.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,read.coercions] }

def substituteWord {source : TypedSource} (word : WordNode source) (substitution : TypeSystem.Substitution) :
    WordNode (source.applySubstitution substitution) := {
  node := word.node.applySubstitution substitution
  literal := word.literal
  resolution := word.resolution.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ word.found
  form := by simp [ExpressionNode.applySubstitution,word.form,ExpressionForm.applySubstitution]
  target := by simp [word.target]
  requirements := by simp [ExpressionNode.applySubstitution,word.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,word.coercions] }

def LambdaShape.descriptor {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (resultType (.variable shape.typeVariable)) [shape.returned.id]

theorem LambdaShape.captures {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

theorem LambdaShape.body_applies {source : TypedSource} (shape : LambdaShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value) (flag : Bool)
    (capturedValue : StoredValue shape.flag captured before (.bool flag))
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] (resultValue argument flag)
      ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument) ⟨copied.cells.length⟩ after := .append
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id,node,_contains,form,_raw,typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_,_,parameters⟩
  obtain ⟨types,callContext,parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      have extending : ∃ types, MonoBindersExtend function.source.owner function.context function.parameters
          types (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) :=
        ⟨_, parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)⟩
      obtain ⟨types,extended⟩ := extending
      obtain ⟨final,facts,bodyTyped,_⟩ := CoreLowering.CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
      obtain ⟨middle,_,_,headTyped,_⟩ := Tests.SourceCoreMixedImperative.head_tail bodyTyped
      have returnedFound := lookupStatement?_complete frame.code.graph.nodeOccurrencesUnique
        (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound))
      have returnedForm : (shape.returned.applySubstitution substitution).form = .returnStmt (some shape.result.node.id) := by
        simp [StatementNode.applySubstitution,shape.returnForm,StatementForm.applySubstitution]
      have original := Tests.SourceCoreMixedImperative.form_at frame.code.graph.nodeOccurrencesUnique returnedFound headTyped
      rw [returnedForm] at original
      cases original with
      | returnValue typed =>
        obtain ⟨_,_,_,extraTyped⟩ := (shape.result.substitute substitution).children frame.code.graph.nodeOccurrencesUnique typed
        obtain ⟨_,_,_,zeroTyped⟩ := (shape.extra.substitute substitution).children frame.code.graph.nodeOccurrencesUnique extraTyped
        have firstStored : StoredValue (shape.parameter.applySubstitution substitution)
            ((parameter.id,⟨copied.cells.length⟩)::entry) after argument := ⟨_,_,.head,allocation.reads_new,rfl,rfl⟩
        have firstTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.first substitution) firstStored
        have secondTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.second substitution) firstStored
        have captureStored : StoredValue (shape.flag.applySubstitution substitution)
            ((parameter.id,⟨copied.cells.length⟩)::entry) after (.bool flag) := by
          rcases capturedValue with ⟨location,cell,lookup,read,ordinary,contents⟩
          obtain ⟨copyLocation,copyLookup,copyRead⟩ := copy_reads copy lookup read
          exact ⟨copyLocation,cell,.tail shape.parameterFlag copyLookup,allocation.preserves_read copyRead,ordinary,contents⟩
        have captureTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.capture substitution) captureStored
        have zeroTrace := (substituteWord shape.zero substitution).evaluates (program := program) evidence
          ((parameter.id,⟨copied.cells.length⟩)::entry) after frame.code.graph.nodeOccurrencesUnique zeroTyped
        have expression := (shape.result.substitute substitution).evaluates
          ((shape.duplicate.substitute substitution).evaluates firstTrace secondTrace)
          ((shape.extra.substitute substitution).evaluates captureTrace zeroTrace)
        apply Dynamic.CallableApplies.closure rfl frame extended copy
        · exact .cons allocation (.nil _ _)
        · apply Dynamic.FunctionStatementsExecute.singleton
            (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound))
          · intro expression impossible; rw [returnedForm] at impossible; cases impossible
          · apply Dynamic.StatementExecutes.returnValue
              (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound)) returnedForm
            simpa only [function,parameter,after,LambdaShape.descriptor,Dynamic.GeneralizedClosure.instantiate,Dynamic.GeneralizedClosure.ofDirectLambda,resultValue,PairAt.substitute,ExpressionNode.applySubstitution,substituteWord,IntegerLiteralResolution.applySubstitution_rawValue,shape.zeroValue] using expression
        · rfl

theorem LambdaShape.invoke {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured argumentsHeap entry copied) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue argument flag) ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
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
      (shape.body_applies captured substitution _ evidence argumentsHeap argument flag capturedValue copy frame)
  · rw [call.coercions]; exact .nil


theorem LambdaShape.instance {source : TypedSource} (shape : LambdaShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?,resultType]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil


theorem LambdaShape.frame {source : TypedSource} (shape : LambdaShape source)
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


theorem LambdaShape.invoke_from_typed {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (evidence : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context call.callee.node.id call.callee.node.type)
    (ground : TypeWellFormed context type)
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
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
      (resultValue argument flag) ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution [(shape.typeVariable, type)]).scheme.body, value := some argument}]⟩ := by
  have wellformed := descriptor_scheme_of_typed runtime.graph.nodeOccurrencesUnique
    call.callee.found call.callee.form typed locals lookup read descriptor
  have descriptorTyped := ((heapTyped cell read.member).generalized_inv descriptor).2
  have frame := shape.frame captured before evidence
    (by simpa only [fields.signatures] using catalog) descriptorTyped fields
    runtime.signatures covers wellformed ground
  exact shape.invoke call captured environment [(shape.typeVariable, type)] evidence [] flag capturedValue
    lookup read descriptor fields (shape.instance evidence wellformed ground) frame argumentTrace copy

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionSourceFirst
/-! Allocate the original generalized closure over the copies of its
environment, evaluate both distinct instances from Source typing, and retain the
copied captured flag across the first call, whose own copies leave it intact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative
open Tests.SourceSemanticsCaptureCopies

 def StoredLambda {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) (flag : Bool) : Prop :=
  ∃ definitionContext captured location cell,
    Dynamic.Environment.LooksUp environment shape.binder.id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = some (shape.descriptor definitionContext captured) ∧
    Dynamic.RuntimeContextFields definitionContext context ∧ StoredValue shape.flag captured heap (.bool flag)

theorem StoredLambda.mono {source : TypedSource} {shape : LambdaShape source}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag) (append : HeapAppends before after) :
    StoredLambda shape context environment after flag := by
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  exact ⟨definitionContext,captured,location,cell,lookup,append.read read,descriptor,fields,capture.mono append⟩

theorem CallShape.typed {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type result : TypeSystem.Ty}
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
      cases arguments with | cons argument _ => exact ⟨_,_,callee,argument⟩

theorem StoredLambda.invoke {program : SourceSemantics.Program} {source : TypedSource}
    {shape : LambdaShape source} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag)
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {argument : ExpressionId} {type result : TypeSystem.Ty} (call : CallShape source shape.binder argument type)
    (builtin : type = .word ∨ type = .bool)
    (typed : ExpressionHasType source context call.node.id result) {value : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument value before) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue value flag) after ∧ HeapAppends before after := by
  obtain ⟨_,_,callee,_⟩ := call.typed state.runtime.graph.nodeOccurrencesUnique typed
  obtain ⟨node,contains,sameType⟩ := callee.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete state.runtime.graph.nodeOccurrencesUnique contains).symm.trans call.callee.found)
  subst node
  have ground : TypeWellFormed context type := by
    rcases builtin with same | same
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .word⟩
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .bool⟩
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  have descriptorTyped := ((state.heapTyped cell read.member).generalized_inv descriptor).2
  have readable : Readable before captured := Readable.of_agrees descriptorTyped.captures
  have trace := shape.invoke_from_typed call captured environment evidence flag state.runtime
    (by simpa only [state.runtime.signatures] using wellFormed.signatures)
    state.covers state.locals state.heapTyped (sameType.symm ▸ callee) ground capture lookup read descriptor fields argumentTrace
    (copies_spec_applySubstitution [(shape.typeVariable, type)] source readable)
  exact ⟨_,trace,(HeapAppends.of_copies source captured before).trans ⟨_,rfl⟩⟩

/-- The generalized `let` copies the environment, then stores the principal
descriptor over the copies. -/
def closureHeap {source : TypedSource} (shape : LambdaShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source environment before).2.cells ++
    [{type := shape.binder.scheme.body, value := none,
      generalized := some (shape.descriptor context (copies source environment before).1)}]⟩

theorem closureHeap_appends {source : TypedSource} (shape : LambdaShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    HeapAppends before (closureHeap shape context environment before) :=
  (HeapAppends.of_copies source environment before).trans ⟨_,rfl⟩

theorem generalized_step {program : SourceSemantics.Program} {source : TypedSource}
    (shape : LambdaShape source) (site : StatementAt source (.letDecl shape.binder (some shape.lambda.id)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (captured : StoredValue shape.flag environment before (.bool flag))
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((shape.binder.id,identityLocation source environment before) :: environment))
      (closureHeap shape context environment before) ∧
    SourceState program source final evidence ((shape.binder.id,identityLocation source environment before) :: environment)
      (closureHeap shape context environment before) ∧
    StoredLambda shape final ((shape.binder.id,identityLocation source environment before) :: environment)
      (closureHeap shape context environment before) flag := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized _ mono _ => rw [shape.scheme] at mono; cases mono
  | letInitializedGeneralized polymorphic _ _ _ extended =>
    have snapshot := copies_spec source (Readable.of_agrees state.locals)
    have allocation : Dynamic.Heap.AllocatesGeneralized (copies source environment before).2
        (shape.descriptor context (copies source environment before).1)
        (identityLocation source environment before) (closureHeap shape context environment before) := .append
    have trace := Dynamic.StatementExecutes.letInitializedGeneralized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq snapshot
      (shape.captures context (copies source environment before).1) polymorphic extended allocation
    have capturedCopy : StoredValue shape.flag (copies source environment before).1
        (closureHeap shape context environment before) (.bool flag) := by
      rcases captured with ⟨location,cell,lookup,read,ordinary,contents⟩
      obtain ⟨copyLocation,copyLookup,copyRead⟩ := copy_reads snapshot lookup read
      exact ⟨copyLocation,cell,copyLookup,allocation.preserves_read copyRead,ordinary,contents⟩
    exact ⟨trace,state.after_statement wellFormed typed trace,
      ⟨context,(copies source environment before).1,_,_,.head,allocation.reads_new,rfl,.ofBinderExtends extended,
        capturedCopy⟩⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next (.returned (outputValue flag)) after ∧ HeapAppends before after := by
  obtain ⟨middle,_,_,firstTyped,tailTyped⟩ := head_tail typed
  obtain ⟨declaration,stateNext,stored⟩ := generalized_step shape.f shape.initialized state wellFormed flagStored firstTyped
  obtain ⟨next,_,_,returnedTyped,_⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨_,_,wordTyped,boolTyped⟩ := shape.tuple.children state.runtime.graph.nodeOccurrencesUnique tupleTyped
    obtain ⟨_,_,_,literalTyped⟩ := shape.wordCall.typed state.runtime.graph.nodeOccurrencesUnique wordTyped
    have literalTrace := shape.literal.evaluates (program := program) evidence ((shape.f.binder.id,identityLocation source environment before)::environment) (closureHeap shape.f context environment before) state.runtime.graph.nodeOccurrencesUnique literalTyped
    rw [shape.literalValue] at literalTrace
    obtain ⟨firstHeap,firstTrace,firstAppend⟩ := stored.invoke stateNext wellFormed shape.wordCall (.inl rfl) wordTyped literalTrace
    have stateAfter := stateNext.after_expression wellFormed wordTyped firstTrace
    have allocatedPrefix : HeapAppends before (closureHeap shape.f context environment before) :=
      closureHeap_appends shape.f context environment before
    have flagNext := ((flagStored.mono allocatedPrefix).under (identityLocation source environment before) shape.fFlag).mono
      firstAppend
    obtain ⟨after,secondTrace,secondAppend⟩ := (stored.mono firstAppend).invoke stateAfter wellFormed
      shape.boolCall (.inr rfl) boolTyped (read_value shape.flagRead flagNext)
    have tupleTrace := shape.tuple.evaluates firstTrace secondTrace
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans (firstAppend.trans secondAppend)⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
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
      (.returned (outputValue flag))
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

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionTyping
/-! The duplicate/captured/numeric regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
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
      "generalized body expression full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "generalized body expression original signature membership")
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
  | _ => throw (IO.userError "generalized body expression original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized body expression original complete cache size")
  IO.println "GENERALIZED_BODY_EXPRESSION_ORIGINAL_TYPING: originals1/cache1"
  IO.println "GENERALIZED_BODY_EXPRESSION_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
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


end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedBodyExpression
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
    (.returned (outputValue flag)) after

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
    (outputValue flag)
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

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedBodyExpression
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
    (outputValue flag)
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

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedBodyExpression
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

end Tests.SourceCoreGeneralizedBodyExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedBodyExpressionRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression.ObservedRuntime
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
  let row ← observeRow fixture.original "duplicate"
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
      require (firstReturned.value == publicOutput true) "first duplicate/captured/numeric public value"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == publicOutput false) "second duplicate/captured/numeric public value"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == publicOutput true) "third duplicate/captured/numeric public value"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,23,44,65]) "generalized body expression Source-certified repeated native heaps changed"
          IO.println "GENERALIZED_BODY_EXPRESSION_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"GENERALIZED_BODY_EXPRESSION_SOURCE_HEAPS: {heaps}"
          IO.println "GENERALIZED_BODY_EXPRESSION_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third generalized body expression certified call did not succeed")
      | _ => throw (IO.userError "second generalized body expression certified call did not succeed")
    | _ => throw (IO.userError "first generalized body expression certified call did not succeed")
  else throw (IO.userError "generalized body expression callable catalog disabled")

end Tests.SourceCoreGeneralizedBodyExpression.ObservedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyProbe
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function duplicate(flag: Bool) returns (((Word, Word), (Bool, Word)), ((Bool, Bool), (Bool, Word))) {",
    "  let f = lam(value) { let unused: Word; let copied = value; { flag; } if (flag) { flag; } return ((value, value), (flag, 0)); };",
    "  return (f(11), f(flag));",
    "}" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}
def publicOutput (flag : Bool) : SourceCorePublicValues.Value :=
  .product (.product (.product (.word (word 11)) (.word (word 11))) (.product (.bool flag) (.word (word 0))))
    (.product (.product (.bool flag) (.bool flag)) (.product (.bool flag) (.word (word 0))))

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | _ => throw (IO.userError s!"{label}: public execution did not succeed")

def nativeProbe : IO Unit := do
  let program ← get "check duplicate" (checkProgram workspace options.checkingFuel)
  let source ← get "compile duplicate" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "complete cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete original/cache"
  let recipe ← get "prepare duplicate" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "root absent")
  let facade ← get "public duplicate" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "true" (← initial.run root.key [.bool true] runOptions)
  require (first.value == publicOutput true) "first duplicate/captured/numeric value"
  let second ← succeeded "false" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == publicOutput false) "second duplicate/captured/numeric value"
  let third ← succeeded "true again" (← second.session.run root.key [.bool true] runOptions)
  require (third.value == publicOutput true) "third duplicate/captured/numeric value"
  IO.println s!"GENERALIZED_LEXICAL_BODY_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,third.session.heapSize]}"
  IO.println "GENERALIZED_LEXICAL_BODY_NATIVE_PASS"
end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
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
      | none => throw (IO.userError "generalized lexical body artifact absent")
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
    | throw (IO.userError "generalized lexical body original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized lexical body original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized lexical body global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized lexical body substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized lexical body ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized lexical body ordinary parameters"
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
    | _ => throw (IO.userError "generalized lexical body unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "generalized lexical body complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "generalized lexical body complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "generalized lexical body complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "duplicate"
  IO.println "GENERALIZED_LEXICAL_BODY_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
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

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodySource
/-! The complete original lambda retains ordinary declarations, scoped discard,
a conditional and the product result with captured Bool and numeric leaf.
Observations record syntax and typing metadata only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read observeRead)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StatementAt)

def resultType (type : TypeSystem.Ty) : TypeSystem.Ty := .product (.product type type) (.product .bool .word)
def resultValue (value : Dynamic.Value) (flag : Bool) : Dynamic.Value :=
  .product (.product value value) (.product (.bool flag) (.word (Word.ofNatModulo 0)))
def outputValue (flag : Bool) : Dynamic.Value :=
  .product (resultValue (.word (Word.ofNatModulo 11)) flag) (resultValue (.bool flag) flag)

structure PairAt (source : TypedSource) (left right : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .tuple [left,right]
  requirements : node.requirements = []
  coercions : node.coercions = []

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Read source binder (.function type (resultType type))
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure LambdaShape (source : TypedSource) where
  binder : TypedBinder
  parameter : TypedBinder
  flag : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  unused : TypedBinder
  copied : TypedBinder
  absent : StatementAt source (.letDecl unused none)
  initializer : Read source parameter (.variable typeVariable)
  initialized : StatementAt source (.letDecl copied (some initializer.node.id))
  scopedRead : Read source flag .bool
  scopedDiscard : StatementAt source (.expression scopedRead.node.id true)
  block : StatementAt source (.block [scopedDiscard.node.id])
  condition : Read source flag .bool
  branchRead : Read source flag .bool
  branchDiscard : StatementAt source (.expression branchRead.node.id true)
  conditional : StatementAt source (.ifThen condition.node.id [branchDiscard.node.id] none)
  unusedScheme : unused.scheme = .mono .word
  copiedScheme : copied.scheme = .mono (.variable typeVariable)
  unusedParameter : unused.id ≠ parameter.id
  copiedParameter : copied.id ≠ parameter.id
  unusedFlag : unused.id ≠ flag.id
  copiedFlag : copied.id ≠ flag.id
  lambda : ExpressionNode
  returned : StatementNode
  first : Read source parameter (.variable typeVariable)
  second : Read source parameter (.variable typeVariable)
  duplicate : PairAt source first.node.id second.node.id
  capture : Read source flag .bool
  zero : WordNode source
  extra : PairAt source capture.node.id zero.node.id
  result : PairAt source duplicate.node.id extra.node.id
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (resultType (.variable typeVariable))⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (resultType (.variable typeVariable)) [absent.node.id,initialized.node.id,block.node.id,conditional.node.id,returned.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  returnFound : source.lookupStatement? returned.id = some returned
  returnForm : returned.form = .returnStmt (some result.node.id)
  zeroValue : zero.resolution.rawValue = 0
  parameterFlag : parameter.id ≠ flag.id

structure Shape (source : TypedSource) where
  f : LambdaShape source
  literal : WordNode source
  flagRead : Read source f.flag .bool
  wordCall : CallShape source f.binder literal.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : PairAt source wordCall.node.id boolCall.node.id
  returned : StatementAt source (.returnStmt (some tuple.node.id))
  inputs : source.inputs = [f.flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : f.flag.scheme = .mono .bool
  literalValue : literal.resolution.rawValue = 11
  fFlag : f.binder.id ≠ f.flag.id
abbrev Shape.flag {source : TypedSource} (shape : Shape source) := shape.f.flag

private def pair (source : TypedSource) (left right : ExpressionId) (node : ExpressionNode) : IO (PairAt source left right) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "pair occurrence"
  let ⟨form⟩ ← observed (node.form = .tuple [left,right]) "pair ordered children"
  let ⟨requirements⟩ ← observed (node.requirements = []) "pair requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "pair coercions"
  return ⟨node,found,form,requirements,coercions⟩

private def call (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId) (type : TypeSystem.Ty)
    (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← observeRead source binder callee (.function type (resultType type))
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "call occurrence"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "call ordered argument"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "call arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "call argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩


def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "original input")
  let [.statement absent,.expression initializer,.statement initializedLocal,.expression scopedRead,
      .statement scopedDiscard,.statement block,.expression condition,.expression branchRead,
      .statement branchDiscard,.statement conditional,.expression first,.expression second,.expression duplicate,.expression capture,.expression zero,
      .expression extra,.expression result,.statement lambdaReturn,.expression lambda,.statement initialized,
      .expression literal,.expression wordCallee,.expression wordCall,.expression flagRead,
      .expression boolCallee,.expression boolCall,.expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "complete original duplicate graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "original generalized binder")
  let .lambda [parameter] _ _ := lambda.form | throw (IO.userError "original lambda")
  let .variable typeVar := parameter.scheme.body | throw (IO.userError "principal parameter")
  let .letDecl unused none := absent.form | throw (IO.userError "absent local")
  let .letDecl copied (some _) := initializedLocal.form | throw (IO.userError "initialized local")
  let initializer ← observeRead source parameter initializer (.variable typeVar)
  let scopedRead ← observeRead source flag scopedRead .bool
  let condition ← observeRead source flag condition .bool
  let branchRead ← observeRead source flag branchRead .bool
  let ⟨absentFound⟩ ← observed (source.lookupStatement? absent.id = some absent) "absent occurrence"
  let ⟨absentForm⟩ ← observed (absent.form = .letDecl unused none) "absent form"
  let ⟨initializedLocalFound⟩ ← observed (source.lookupStatement? initializedLocal.id = some initializedLocal) "local initializer occurrence"
  let ⟨initializedLocalForm⟩ ← observed (initializedLocal.form = .letDecl copied (some initializer.node.id)) "local initializer form"
  let ⟨scopedDiscardFound⟩ ← observed (source.lookupStatement? scopedDiscard.id = some scopedDiscard) "scoped discard occurrence"
  let ⟨scopedDiscardForm⟩ ← observed (scopedDiscard.form = .expression scopedRead.node.id true) "scoped discard form"
  let ⟨blockFound⟩ ← observed (source.lookupStatement? block.id = some block) "block occurrence"
  let ⟨blockForm⟩ ← observed (block.form = .block [scopedDiscard.id]) "block form"
  let ⟨branchDiscardFound⟩ ← observed (source.lookupStatement? branchDiscard.id = some branchDiscard) "branch discard occurrence"
  let ⟨branchDiscardForm⟩ ← observed (branchDiscard.form = .expression branchRead.node.id true) "branch discard form"
  let ⟨conditionalFound⟩ ← observed (source.lookupStatement? conditional.id = some conditional) "conditional occurrence"
  let ⟨conditionalForm⟩ ← observed (conditional.form = .ifThen condition.node.id [branchDiscard.id] none) "conditional form"
  let ⟨unusedScheme⟩ ← observed (unused.scheme = .mono .word) "absent local scheme"
  let ⟨copiedScheme⟩ ← observed (copied.scheme = .mono (.variable typeVar)) "initialized local scheme"
  let ⟨unusedParameter⟩ ← observed (unused.id ≠ parameter.id) "absent and parameter distinct"
  let ⟨copiedParameter⟩ ← observed (copied.id ≠ parameter.id) "copied and parameter distinct"
  let ⟨unusedFlag⟩ ← observed (unused.id ≠ flag.id) "absent and capture distinct"
  let ⟨copiedFlag⟩ ← observed (copied.id ≠ flag.id) "copied and capture distinct"
  let first ← observeRead source parameter first (.variable typeVar)
  let second ← observeRead source parameter second (.variable typeVar)
  let duplicate ← pair source first.node.id second.node.id duplicate
  let capture ← observeRead source flag capture .bool
  let zero ← wordNode source zero
  let extra ← pair source capture.node.id zero.node.id extra
  let result ← pair source duplicate.node.id extra.node.id result
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (resultType (.variable typeVar))⟩) "principal duplicate scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "parameter scheme"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "parameter requirements"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "lambda occurrence"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (resultType (.variable typeVar)) [absent.id,initializedLocal.id,block.id,conditional.id,lambdaReturn.id]) "lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "lambda raw"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "lambda type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? lambdaReturn.id = some lambdaReturn) "lambda return occurrence"
  let ⟨returnForm⟩ ← observed (lambdaReturn.form = .returnStmt (some result.node.id)) "lambda return expression"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "numeric leaf zero"
  let ⟨parameterFlag⟩ ← observed (parameter.id ≠ flag.id) "captured binder differs"
  let f : LambdaShape source := ⟨binder,parameter,flag,typeVar,unused,copied,⟨absent,absentFound,absentForm⟩,initializer,
    ⟨initializedLocal,initializedLocalFound,initializedLocalForm⟩,scopedRead,
    ⟨scopedDiscard,scopedDiscardFound,scopedDiscardForm⟩,⟨block,blockFound,blockForm⟩,condition,branchRead,
    ⟨branchDiscard,branchDiscardFound,branchDiscardForm⟩,⟨conditional,conditionalFound,conditionalForm⟩,
    unusedScheme,copiedScheme,unusedParameter,copiedParameter,unusedFlag,copiedFlag,
    lambda,lambdaReturn,first,second,duplicate,capture,zero,extra,result,
    scheme,requirements,parameterScheme,parameterRequirements,lambdaFound,lambdaForm,lambdaRaw,lambdaType,
    lambdaRequirements,lambdaCoercions,returnFound,returnForm,zeroValue,parameterFlag⟩
  let literal ← wordNode source literal
  let flagRead ← observeRead source flag flagRead .bool
  let wordCall ← call source binder literal.node.id .word wordCallee wordCall
  let boolCall ← call source binder flagRead.node.id .bool boolCallee boolCall
  let tuple ← pair source wordCall.node.id boolCall.node.id tuple
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration occurrence"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return occurrence"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.node.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [f.flag]) "complete original parameters"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "complete original roots"
  let ⟨flagScheme⟩ ← observed (f.flag.scheme = .mono .bool) "flag scheme"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "argument literal"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ f.flag.id) "capture distinct from declaration"
  return ⟨f,literal,flagRead,wordCall,boolCall,⟨initialized,initializedFound,initializedForm⟩,tuple,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,literalValue,fFlag⟩

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyCalls
/-! Source evaluation is built from the original lambda, the call's copy of
its actual captured cell and the instantiated static frame. No Core run
supplies a body trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedLexicalBody
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StoredValue)
open Tests.SourceSemanticsCaptureCopies (copy_reads)

 theorem PairAt.children {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context pair.node.id type) :
    ∃ leftType rightType, ExpressionHasType source context left leftType ∧ ExpressionHasType source context right rightType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans pair.found)
    rw [pair.form] at raw
    cases raw with
    | tuple children => cases children with | cons first tail => cases tail with | cons second _ => exact ⟨_,_,first,second⟩

theorem PairAt.evaluates {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {first second : Dynamic.Value}
    (a : Dynamic.ExpressionEvaluates program context evidence source environment before left first middle)
    (b : Dynamic.ExpressionEvaluates program context evidence source environment middle right second after) :
    Dynamic.ExpressionEvaluates program context evidence source environment before pair.node.id (.product first second) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound pair.found)
  · rw [pair.form,pair.requirements,pair.coercions]
    exact .tuple rfl (.cons a (.cons b .nil)) (.cons (.singleton _))
  · rw [pair.coercions]; exact .nil

def PairAt.substitute {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) (substitution : TypeSystem.Substitution) :
    PairAt (source.applySubstitution substitution) left right := {
  node := pair.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ pair.found
  form := by simp [ExpressionNode.applySubstitution,pair.form,ExpressionForm.applySubstitution]
  requirements := by simp [ExpressionNode.applySubstitution,pair.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,pair.coercions] }

def substituteRead {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Read source binder type) (substitution : TypeSystem.Substitution) :
    Read (source.applySubstitution substitution) (binder.applySubstitution substitution) (substitution.apply type) := {
  node := read.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ read.found
  form := by simp [ExpressionNode.applySubstitution,read.form,ExpressionForm.applySubstitution,TypedBinder.applySubstitution,ReferenceResolution.applySubstitution]
  raw := by simp [ExpressionNode.rawType,ExpressionNode.applySubstitution,read.coercions,read.type]
  type := by simp [ExpressionNode.applySubstitution,read.type]
  requirements := by simp [ExpressionNode.applySubstitution,read.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,read.coercions] }

def substituteWord {source : TypedSource} (word : WordNode source) (substitution : TypeSystem.Substitution) :
    WordNode (source.applySubstitution substitution) := {
  node := word.node.applySubstitution substitution
  literal := word.literal
  resolution := word.resolution.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ word.found
  form := by simp [ExpressionNode.applySubstitution,word.form,ExpressionForm.applySubstitution]
  target := by simp [word.target]
  requirements := by simp [ExpressionNode.applySubstitution,word.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,word.coercions] }

def LambdaShape.descriptor {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (resultType (.variable shape.typeVariable)) [shape.absent.node.id,shape.initialized.node.id,shape.block.node.id,shape.conditional.node.id,shape.returned.id]

theorem LambdaShape.captures {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

theorem LambdaShape.body_applies {source : TypedSource} (shape : LambdaShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value) (flag : Bool)
    (capturedValue : StoredValue shape.flag captured before (.bool flag))
    {entry : Dynamic.Environment} {copiedHeap : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copiedHeap)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    ∃ after, Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] (resultValue argument flag) after ∧ Tests.SourceCoreMixedImperative.HeapAppends before after := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let unused := shape.unused.applySubstitution substitution
  let copied := shape.copied.applySubstitution substitution
  let bound : Dynamic.Heap := ⟨copiedHeap.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  let middle : Dynamic.Heap := ⟨bound.cells ++ [{type := unused.scheme.body, value := none}]⟩
  let after : Dynamic.Heap := ⟨middle.cells ++ [{type := copied.scheme.body, value := some argument}]⟩
  let parameterEnv := (parameter.id,⟨copiedHeap.cells.length⟩)::entry
  let unusedEnv := (unused.id,⟨bound.cells.length⟩)::parameterEnv
  let localEnv := (copied.id,⟨middle.cells.length⟩)::unusedEnv
  have allocation : Dynamic.Heap.Allocates copiedHeap parameter.scheme.body (some argument) ⟨copiedHeap.cells.length⟩ bound := .append
  have absentAllocation : Dynamic.Heap.Allocates bound unused.scheme.body none ⟨bound.cells.length⟩ middle := .append
  have copiedAllocation : Dynamic.Heap.Allocates middle copied.scheme.body (some argument) ⟨middle.cells.length⟩ after := .append
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id,node,_contains,form,_raw,typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_,_,parameters⟩
  obtain ⟨types,callContext,parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      have extending : ∃ types, MonoBindersExtend function.source.owner function.context function.parameters
          types (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) :=
        ⟨_, parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)⟩
      obtain ⟨types,extended⟩ := extending
      obtain ⟨final,facts,bodyTyped,_⟩ := CoreLowering.CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
      have unique := frame.code.graph.nodeOccurrencesUnique
      have absentContains := FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.absent.found)
      have absentForm : (shape.absent.node.applySubstitution substitution).form = .letDecl unused none := by
        simp [StatementNode.applySubstitution,shape.absent.formEq,StatementForm.applySubstitution,unused]
      have initContains := FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.initialized.found)
      have initForm : (shape.initialized.node.applySubstitution substitution).form = .letDecl copied (some shape.initializer.node.id) := by
        simp [StatementNode.applySubstitution,shape.initialized.formEq,StatementForm.applySubstitution,copied]
      obtain ⟨absentContext,_,_,absentTyped,afterAbsent⟩ := Tests.SourceCoreMixedImperative.head_tail bodyTyped
      have absentOriginal := Tests.SourceCoreMixedImperative.form_at unique (lookupStatement?_complete unique absentContains) absentTyped
      rw [absentForm] at absentOriginal
      cases absentOriginal with
      | letUninitialized absentMono absentExtended =>
        obtain ⟨localContext,_,_,initTyped,afterInit⟩ := Tests.SourceCoreMixedImperative.head_tail afterAbsent
        have initOriginal := Tests.SourceCoreMixedImperative.form_at unique (lookupStatement?_complete unique initContains) initTyped
        rw [initForm] at initOriginal
        have copiedMono : copied.scheme.quantified = [] := by simp [copied,TypedBinder.applySubstitution,shape.copiedScheme,TypeSystem.Scheme.mono]
        cases initOriginal with
        | letInitializedGeneralized polymorphic => exact False.elim (polymorphic copiedMono)
        | letInitialized initializerTyped _ copiedExtended =>
          obtain ⟨blockContext,_,_,blockTyped,afterBlock⟩ := Tests.SourceCoreMixedImperative.head_tail afterInit
          have blockContains := FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.block.found)
          have blockForm : (shape.block.node.applySubstitution substitution).form = .block [shape.scopedDiscard.node.id] := by
            simp [StatementNode.applySubstitution,shape.block.formEq,StatementForm.applySubstitution]
          have blockOriginal := Tests.SourceCoreMixedImperative.form_at unique (lookupStatement?_complete unique blockContains) blockTyped
          rw [blockForm] at blockOriginal
          cases blockOriginal with
          | block _ =>
            obtain ⟨conditionContext,_,_,conditionTyped,afterCondition⟩ := Tests.SourceCoreMixedImperative.head_tail afterBlock
            have conditionContains := FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.conditional.found)
            have conditionForm : (shape.conditional.node.applySubstitution substitution).form =
                .ifThen shape.condition.node.id [shape.branchDiscard.node.id] none := by
              simp [StatementNode.applySubstitution,shape.conditional.formEq,StatementForm.applySubstitution]
            have conditionOriginal := Tests.SourceCoreMixedImperative.form_at unique (lookupStatement?_complete unique conditionContains) conditionTyped
            rw [conditionForm] at conditionOriginal
            cases conditionOriginal with
            | ifWithoutElse _ _ =>
              obtain ⟨returnedContext,_,_,headTyped,_⟩ := Tests.SourceCoreMixedImperative.head_tail afterCondition
              have returnedContains := FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound)
              have returnedFound := lookupStatement?_complete unique returnedContains
              have returnedForm : (shape.returned.applySubstitution substitution).form = .returnStmt (some shape.result.node.id) := by
                simp [StatementNode.applySubstitution,shape.returnForm,StatementForm.applySubstitution]
              have original := Tests.SourceCoreMixedImperative.form_at unique returnedFound headTyped
              rw [returnedForm] at original
              cases original with
              | returnValue typed =>
                obtain ⟨_,_,_,extraTyped⟩ := (shape.result.substitute substitution).children unique typed
                obtain ⟨_,_,_,zeroTyped⟩ := (shape.extra.substitute substitution).children unique extraTyped
                have parameterStored : StoredValue parameter parameterEnv bound argument := ⟨_,_,.head,allocation.reads_new,rfl,rfl⟩
                have unusedAppend : Tests.SourceCoreMixedImperative.HeapAppends bound middle := ⟨_,rfl⟩
                have copiedAppend : Tests.SourceCoreMixedImperative.HeapAppends middle after := ⟨_,rfl⟩
                have initialStored : StoredValue parameter unusedEnv middle argument :=
                  (parameterStored.mono unusedAppend).under _ shape.unusedParameter
                have finalStored : StoredValue parameter localEnv after argument :=
                  (initialStored.mono copiedAppend).under _ shape.copiedParameter
                have initialTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := absentContext)
                  (evidence := evidence) (substituteRead shape.initializer substitution) initialStored
                have firstTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.first substitution) finalStored
                have secondTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.second substitution) finalStored
                have capturedBound : StoredValue (shape.flag.applySubstitution substitution) parameterEnv bound (.bool flag) := by
                  rcases capturedValue with ⟨location,cell,lookup,read,ordinary,contents⟩
                  obtain ⟨copyLocation,copyLookup,copyRead⟩ := copy_reads copy lookup read
                  exact ⟨copyLocation,cell,.tail shape.parameterFlag copyLookup,allocation.preserves_read copyRead,
                    ordinary,contents⟩
                have captureStored : StoredValue (shape.flag.applySubstitution substitution) localEnv after (.bool flag) :=
                  (((capturedBound.mono unusedAppend).under _ shape.unusedFlag).mono copiedAppend).under _ shape.copiedFlag
                have captureTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.capture substitution) captureStored
                have scopedTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.scopedRead substitution) captureStored
                have conditionTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.condition substitution) captureStored
                have branchTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := localContext)
                  (evidence := evidence) (substituteRead shape.branchRead substitution) captureStored
                have zeroTrace := (substituteWord shape.zero substitution).evaluates (program := program) evidence
                  localEnv after unique zeroTyped
                have expression := (shape.result.substitute substitution).evaluates
                  ((shape.duplicate.substitute substitution).evaluates firstTrace secondTrace)
                  ((shape.extra.substitute substitution).evaluates captureTrace zeroTrace)
                have blockTrace : Dynamic.StatementExecutes program localContext evidence function.source localEnv after
                    shape.block.node.id localContext (.fallthrough localEnv) after := by
                  apply Dynamic.StatementExecutes.block (outcome := .fallthrough localEnv) blockContains blockForm
                  apply Dynamic.StatementsExecute.cons
                  · apply Dynamic.StatementExecutes.expression (expression := shape.scopedRead.node.id) (semicolon := true)
                      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.scopedDiscard.found))
                    · simp [StatementNode.applySubstitution,shape.scopedDiscard.formEq,StatementForm.applySubstitution]
                    · exact scopedTrace
                  · exact .nil
                have ifTrace : Dynamic.StatementExecutes program localContext evidence function.source localEnv after
                    shape.conditional.node.id localContext (.fallthrough localEnv) after := by
                  cases flag with
                  | false => exact .ifFalseWithoutElse conditionContains conditionForm conditionTrace
                  | true =>
                    apply Dynamic.StatementExecutes.ifTrue (outcome := .fallthrough localEnv) conditionContains conditionForm conditionTrace
                    apply Dynamic.StatementsExecute.cons
                    · apply Dynamic.StatementExecutes.expression (expression := shape.branchRead.node.id) (semicolon := true)
                        (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.branchDiscard.found))
                      · simp [StatementNode.applySubstitution,shape.branchDiscard.formEq,StatementForm.applySubstitution]
                      · exact branchTrace
                    · exact .nil
                refine ⟨after,?_,?_⟩
                · apply Dynamic.CallableApplies.closure rfl frame extended copy
                  · exact .cons allocation (.nil _ _)
                  · apply Dynamic.FunctionStatementsExecute.cons
                      (.letUninitialized absentContains absentForm absentMono absentExtended absentAllocation)
                    apply Dynamic.FunctionStatementsExecute.cons
                      (.letInitialized initContains initForm initialTrace copiedMono copiedExtended copiedAllocation)
                    apply Dynamic.FunctionStatementsExecute.cons blockTrace
                    apply Dynamic.FunctionStatementsExecute.cons ifTrace
                    apply Dynamic.FunctionStatementsExecute.singleton returnedContains
                    · intro expression impossible; rw [returnedForm] at impossible; cases impossible
                    · apply Dynamic.StatementExecutes.returnValue returnedContains returnedForm
                      simpa only [resultValue,PairAt.substitute,ExpressionNode.applySubstitution,substituteWord,
                        IntegerLiteralResolution.applySubstitution_rawValue,shape.zeroValue] using expression
                  · rfl
                · refine (Tests.SourceCoreMixedImperative.HeapAppends.of_environmentCopies copy).trans
                    ⟨[{type := parameter.scheme.body, value := some argument},
                    {type := unused.scheme.body, value := none},
                    {type := copied.scheme.body, value := some argument}],?_⟩
                  simp only [after,middle,bound,List.append_assoc,List.cons_append,List.nil_append]


theorem LambdaShape.invoke {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copiedHeap : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured argumentsHeap entry copiedHeap) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue argument flag) after ∧ Tests.SourceCoreMixedImperative.HeapAppends argumentsHeap after := by
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
  obtain ⟨after,body,append⟩ := shape.body_applies captured substitution _ evidence argumentsHeap argument flag capturedValue
    copy frame
  refine ⟨after,?_,append⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      body
  · rw [call.coercions]; exact .nil


theorem LambdaShape.instance {source : TypedSource} (shape : LambdaShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?,resultType]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil


theorem LambdaShape.frame {source : TypedSource} (shape : LambdaShape source)
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


theorem LambdaShape.invoke_from_typed {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (evidence : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context call.callee.node.id call.callee.node.type)
    (ground : TypeWellFormed context type)
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copiedHeap : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution [(shape.typeVariable, type)]) captured
      argumentsHeap entry copiedHeap) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue argument flag) after ∧ Tests.SourceCoreMixedImperative.HeapAppends argumentsHeap after := by
  have wellformed := descriptor_scheme_of_typed runtime.graph.nodeOccurrencesUnique
    call.callee.found call.callee.form typed locals lookup read descriptor
  have descriptorTyped := ((heapTyped cell read.member).generalized_inv descriptor).2
  have frame := shape.frame captured before evidence
    (by simpa only [fields.signatures] using catalog) descriptorTyped fields
    runtime.signatures covers wellformed ground
  exact shape.invoke call captured environment [(shape.typeVariable, type)] evidence [] flag capturedValue
    lookup read descriptor fields (shape.instance evidence wellformed ground) frame argumentTrace copy

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodySourceFirst
/-! Allocate the original generalized closure over the copies of its
environment, evaluate both distinct instances from Source typing, and retain the
copied captured flag across the first call, whose own copies leave it intact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative
open Tests.SourceSemanticsCaptureCopies

 def StoredLambda {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) (flag : Bool) : Prop :=
  ∃ definitionContext captured location cell,
    Dynamic.Environment.LooksUp environment shape.binder.id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = some (shape.descriptor definitionContext captured) ∧
    Dynamic.RuntimeContextFields definitionContext context ∧ StoredValue shape.flag captured heap (.bool flag)

theorem StoredLambda.mono {source : TypedSource} {shape : LambdaShape source}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag) (append : HeapAppends before after) :
    StoredLambda shape context environment after flag := by
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  exact ⟨definitionContext,captured,location,cell,lookup,append.read read,descriptor,fields,capture.mono append⟩

theorem CallShape.typed {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type result : TypeSystem.Ty}
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
      cases arguments with | cons argument _ => exact ⟨_,_,callee,argument⟩

theorem StoredLambda.invoke {program : SourceSemantics.Program} {source : TypedSource}
    {shape : LambdaShape source} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag)
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {argument : ExpressionId} {type result : TypeSystem.Ty} (call : CallShape source shape.binder argument type)
    (builtin : type = .word ∨ type = .bool)
    (typed : ExpressionHasType source context call.node.id result) {value : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument value before) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue value flag) after ∧ HeapAppends before after := by
  obtain ⟨_,_,callee,_⟩ := call.typed state.runtime.graph.nodeOccurrencesUnique typed
  obtain ⟨node,contains,sameType⟩ := callee.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete state.runtime.graph.nodeOccurrencesUnique contains).symm.trans call.callee.found)
  subst node
  have ground : TypeWellFormed context type := by
    rcases builtin with same | same
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .word⟩
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .bool⟩
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  have descriptorTyped := ((state.heapTyped cell read.member).generalized_inv descriptor).2
  have readable : Readable before captured := Readable.of_agrees descriptorTyped.captures
  exact shape.invoke_from_typed call captured environment evidence flag state.runtime
    (by simpa only [state.runtime.signatures] using wellFormed.signatures)
    state.covers state.locals state.heapTyped (sameType.symm ▸ callee) ground capture lookup read descriptor fields argumentTrace
    (copies_spec_applySubstitution [(shape.typeVariable, type)] source readable)

/-- The generalized `let` copies the environment, then stores the principal
descriptor over the copies. -/
def closureHeap {source : TypedSource} (shape : LambdaShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source environment before).2.cells ++
    [{type := shape.binder.scheme.body, value := none,
      generalized := some (shape.descriptor context (copies source environment before).1)}]⟩

theorem closureHeap_appends {source : TypedSource} (shape : LambdaShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    HeapAppends before (closureHeap shape context environment before) :=
  (HeapAppends.of_copies source environment before).trans ⟨_,rfl⟩

theorem generalized_step {program : SourceSemantics.Program} {source : TypedSource}
    (shape : LambdaShape source) (site : StatementAt source (.letDecl shape.binder (some shape.lambda.id)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (captured : StoredValue shape.flag environment before (.bool flag))
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((shape.binder.id,identityLocation source environment before) :: environment))
      (closureHeap shape context environment before) ∧
    SourceState program source final evidence ((shape.binder.id,identityLocation source environment before) :: environment)
      (closureHeap shape context environment before) ∧
    StoredLambda shape final ((shape.binder.id,identityLocation source environment before) :: environment)
      (closureHeap shape context environment before) flag := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized _ mono _ => rw [shape.scheme] at mono; cases mono
  | letInitializedGeneralized polymorphic _ _ _ extended =>
    have snapshot := copies_spec source (Readable.of_agrees state.locals)
    have allocation : Dynamic.Heap.AllocatesGeneralized (copies source environment before).2
        (shape.descriptor context (copies source environment before).1)
        (identityLocation source environment before) (closureHeap shape context environment before) := .append
    have trace := Dynamic.StatementExecutes.letInitializedGeneralized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq snapshot
      (shape.captures context (copies source environment before).1) polymorphic extended allocation
    have capturedCopy : StoredValue shape.flag (copies source environment before).1
        (closureHeap shape context environment before) (.bool flag) := by
      rcases captured with ⟨location,cell,lookup,read,ordinary,contents⟩
      obtain ⟨copyLocation,copyLookup,copyRead⟩ := copy_reads snapshot lookup read
      exact ⟨copyLocation,cell,copyLookup,allocation.preserves_read copyRead,ordinary,contents⟩
    exact ⟨trace,state.after_statement wellFormed typed trace,
      ⟨context,(copies source environment before).1,_,_,.head,allocation.reads_new,rfl,.ofBinderExtends extended,
        capturedCopy⟩⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next (.returned (outputValue flag)) after ∧ HeapAppends before after := by
  obtain ⟨middle,_,_,firstTyped,tailTyped⟩ := head_tail typed
  obtain ⟨declaration,stateNext,stored⟩ := generalized_step shape.f shape.initialized state wellFormed flagStored firstTyped
  obtain ⟨next,_,_,returnedTyped,_⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨_,_,wordTyped,boolTyped⟩ := shape.tuple.children state.runtime.graph.nodeOccurrencesUnique tupleTyped
    obtain ⟨_,_,_,literalTyped⟩ := shape.wordCall.typed state.runtime.graph.nodeOccurrencesUnique wordTyped
    have literalTrace := shape.literal.evaluates (program := program) evidence ((shape.f.binder.id,identityLocation source environment before)::environment) (closureHeap shape.f context environment before) state.runtime.graph.nodeOccurrencesUnique literalTyped
    rw [shape.literalValue] at literalTrace
    obtain ⟨firstHeap,firstTrace,firstAppend⟩ := stored.invoke stateNext wellFormed shape.wordCall (.inl rfl) wordTyped literalTrace
    have stateAfter := stateNext.after_expression wellFormed wordTyped firstTrace
    have allocatedPrefix : HeapAppends before (closureHeap shape.f context environment before) :=
      closureHeap_appends shape.f context environment before
    have flagNext := ((flagStored.mono allocatedPrefix).under (identityLocation source environment before) shape.fFlag).mono
      firstAppend
    obtain ⟨after,secondTrace,secondAppend⟩ := (stored.mono firstAppend).invoke stateAfter wellFormed
      shape.boolCall (.inr rfl) boolTyped (read_value shape.flagRead flagNext)
    have tupleTrace := shape.tuple.evaluates firstTrace secondTrace
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans (firstAppend.trans secondAppend)⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodySelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
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
      (.returned (outputValue flag))
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

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyTyping
/-! The complete lexical-body regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
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
      "generalized lexical body full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "generalized lexical body original signature membership")
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
  | _ => throw (IO.userError "generalized lexical body original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized lexical body original complete cache size")
  IO.println "GENERALIZED_LEXICAL_BODY_ORIGINAL_TYPING: originals1/cache1"
  IO.println "GENERALIZED_LEXICAL_BODY_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
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


end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedLexicalBody
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
    (.returned (outputValue flag)) after

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
    (outputValue flag)
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

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedLexicalBody
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
    (outputValue flag)
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

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedLexicalBody
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

end Tests.SourceCoreGeneralizedLexicalBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralizedLexicalBodyRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody.ObservedRuntime
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
  let row ← observeRow fixture.original "duplicate"
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
      require (firstReturned.value == publicOutput true) "first duplicate/captured/numeric public value"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == publicOutput false) "second duplicate/captured/numeric public value"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == publicOutput true) "third duplicate/captured/numeric public value"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,35,68,101]) "generalized lexical body Source-certified repeated native heaps changed"
          IO.println "GENERALIZED_LEXICAL_BODY_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"GENERALIZED_LEXICAL_BODY_SOURCE_HEAPS: {heaps}"
          IO.println "GENERALIZED_LEXICAL_BODY_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third generalized lexical body certified call did not succeed")
      | _ => throw (IO.userError "second generalized lexical body certified call did not succeed")
    | _ => throw (IO.userError "first generalized lexical body certified call did not succeed")
  else throw (IO.userError "generalized lexical body callable catalog disabled")

end Tests.SourceCoreGeneralizedLexicalBody.ObservedRuntime
end
