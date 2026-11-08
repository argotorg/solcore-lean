import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.Test.SourceSemantics.Semantics
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.Test.SourceSemantics.CoreLowering.Selected.GeneralizedSource
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHandles
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicForward
import Solcore.SourceSemantics.CoreLowering.PublicSessions

/-!
# Interleaved selected tests

Interleaved local selection of generalized identities.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalSource
/-! One unchanged original function captures an identity lambda as a generalized
local, stores its Word call result in an ordinary local, then calls the Bool instance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Core Frontend SourceInference SourceSemantics

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(value) { return value; }; let x = f(11); return (x, f(flag)); }"}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Tests.SourceCoreNamedBranch.Read source binder (.function type type)
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  initialized : StatementNode
  lambda : ExpressionNode
  identityReturn : StatementNode
  parameterRead : Tests.SourceCoreNamedBranch.Read source parameter (.variable typeVariable)
  literal : WordNode source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source binder literal.node.id .word
  boolCall : CallShape source binder flagRead.node.id .bool
  valueBinder : TypedBinder
  valueInitialized : StatementNode
  valueRead : Tests.SourceCoreNamedBranch.Read source valueBinder .word
  tuple : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [flag]
  flagScheme : flag.scheme = .mono .bool
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  valueScheme : valueBinder.scheme = .mono .word
  roots : source.roots = [.statement initialized.id, .statement valueInitialized.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  identityFound : source.lookupStatement? identityReturn.id = some identityReturn
  identityForm : identityReturn.form = .returnStmt (some parameterRead.node.id)
  literalValue : literal.resolution.rawValue = 11
  valueFound : source.lookupStatement? valueInitialized.id = some valueInitialized
  valueForm : valueInitialized.form = .letDecl valueBinder (some wordCall.node.id)
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [valueRead.node.id, boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

def Shape.descriptor {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (.variable shape.typeVariable) [shape.identityReturn.id]

def Shape.allocatedHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment) }]⟩

theorem Shape.captures {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

/-- The original let copies its environment once and stores one principal
descriptor over the copies. It performs no lambda body call and selects
neither the Word nor Bool instance at allocation. -/
theorem Shape.initializes {source : TypedSource} (shape : Shape source)
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

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
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
      | none => throw (IO.userError "generalized local artifact absent")
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
    | throw (IO.userError "generalized local original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized local original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized local global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized local substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized local ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized local ordinary parameters"
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
    | _ => throw (IO.userError "generalized local unique physical slot")

def observeCall (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId)
    (type : TypeSystem.Ty) (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder callee (.function type type)
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "generalized original indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "generalized call identity"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "generalized call order"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "generalized original arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "generalized argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "generalized call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "generalized call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "generalized input")
  let [.expression parameterNode,.statement identityReturn,.expression lambda,.statement initialized,
       .expression literalNode,.expression wordCallee,.expression first,.statement valueInitialized,
       .expression valueNode,.expression flagNode,.expression boolCallee,.expression second,
       .expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "generalized original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "generalized original binder")
  let .lambda [parameter] (.variable typeVariable) _ := lambda.form
    | throw (IO.userError "generalized principal lambda")
  let .letDecl valueBinder _ := valueInitialized.form | throw (IO.userError "interleaved ordinary binder")
  let valueRead ← Tests.SourceCoreNamedBranch.observeRead source valueBinder valueNode .word
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVariable)
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let .integerLiteral raw resolution := literalNode.form | throw (IO.userError "generalized original literal")
  let ⟨literalFound⟩ ← observed (source.lookupExpression? literalNode.id = some literalNode) "generalized literal identity"
  let ⟨literalForm⟩ ← observed (literalNode.form = .integerLiteral raw resolution) "generalized literal form"
  let ⟨literalTarget⟩ ← observed (resolution.targetType = .word) "generalized literal Word"
  let ⟨literalRequirements⟩ ← observed (literalNode.requirements = [resolution.requirement]) "generalized literal requirements"
  let ⟨literalCoercions⟩ ← observed (literalNode.coercions = []) "generalized literal coercions"
  let literal : WordNode source :=
    ⟨literalNode,raw,resolution,literalFound,literalForm,literalTarget,literalRequirements,literalCoercions⟩
  let wordCall ← observeCall source binder literalNode.id .word wordCallee first
  let boolCall ← observeCall source binder flagRead.node.id .bool boolCallee second
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "generalized original inputs"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "generalized Bool input"
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩) "generalized principal scheme"
  let ⟨schemeRequirements⟩ ← observed (binder.schemeRequirements = []) "generalized principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVariable)) "generalized principal parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "generalized parameter requirements"
  let ⟨valueScheme⟩ ← observed (valueBinder.scheme = .mono .word) "interleaved ordinary scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement valueInitialized.id,.statement returned.id]) "generalized original root order"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "generalized let identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl binder (some lambda.id)) "generalized let initializer"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "generalized lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]) "generalized original lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "generalized principal raw type"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "generalized principal result type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "generalized initializer requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "generalized initializer coercions"
  let ⟨identityFound⟩ ← observed (source.lookupStatement? identityReturn.id = some identityReturn) "generalized identity return lookup"
  let ⟨identityForm⟩ ← observed (identityReturn.form = .returnStmt (some parameterRead.node.id)) "generalized identity return form"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "generalized original literal value"
  let ⟨valueFound⟩ ← observed (source.lookupStatement? valueInitialized.id = some valueInitialized) "interleaved ordinary let identity"
  let ⟨valueForm⟩ ← observed (valueInitialized.form = .letDecl valueBinder (some wordCall.node.id)) "interleaved ordinary initializer"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "generalized tuple lookup"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [valueRead.node.id,boolCall.node.id]) "generalized ordered calls"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "generalized tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "generalized tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "generalized outer return lookup"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "generalized outer return form"
  return ⟨flag,binder,parameter,typeVariable,initialized,lambda,identityReturn,parameterRead,literal,flagRead,
    wordCall,boolCall,valueBinder,valueInitialized,valueRead,tuple,returned,inputs,flagScheme,scheme,schemeRequirements,parameterScheme,
    parameterRequirements,valueScheme,roots,initializedFound,initializedForm,lambdaFound,lambdaForm,lambdaRaw,
    lambdaType,lambdaRequirements,lambdaCoercions,identityFound,identityForm,literalValue,
    valueFound,valueForm,tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩

/-- Runtime observation only. The separate Source proofs do not use these
completed target executions as premises. -/
def probe : IO Unit := do
  let fixture ← compileFixture
  let row ← observeRow fixture "local"
  let _shape ← observeShape row.original.function.typedBody
  unless fixture.recipe.compiled.sourceProgram.functions.length == 1 &&
      fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized complete original cache changed")
  let [named] := fixture.recipe.compiled.indexed.base.functions
    | throw (IO.userError "interleaved original cache")
  let source := CallableIndexedNamedGeneration.source named
  let statements := source.roots.filterMap (fun root => match root with
    | .statement id => some id
    | .expression _ => none)
  let some _profile := CellAwareLexicalNamedBodyProducer.profile? fixture.recipe.compiled.indexed named statements
      named.specialized.function.inferredBodyType
    | throw (IO.userError "interleaved complete original profile")
  let artifact ← fixture.facade.open
  let session ← Tests.SourceCompilerFeatureSupport.boot artifact
  let mut current := session
  let mut heaps := [current.heapSize]
  for flag in [true,false,true] do
    match ← current.run row.original.key [.bool flag] runOptions with
    | .ok (.succeeded returned) =>
      unless returned.value == .product (.word (Word.ofNatModulo 11)) (.bool flag) do
        throw (IO.userError "generalized original result changed")
      current := returned.session
      heaps := heaps ++ [current.heapSize]
    | _ => throw (IO.userError "generalized original runtime failed")
  IO.println s!"INTERLEAVED_LOCAL_ORIGINAL_CACHE: originals1/cache1/profile1"
  IO.println s!"INTERLEAVED_LOCAL_NATIVE_HEAPS: {heaps}"
  IO.println "INTERLEAVED_LOCAL_RUNTIME_PROBE_PASS"

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalProgramProfile
/-! The unchanged original program retains a profile for every actual cached
named row. This packet certifies compiler syntax and preparation; original
declarative program typing remains a separate proof obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareLexicalNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  if originals : original.recipe.compiled.sourceProgram.functions.length = 1 then
    if cached : original.recipe.compiled.indexed.base.functions.length = 1 then
      match CellAwareLexicalNamedProgramProfiles.profile? original.recipe.compiled.indexed with
      | none => throw (IO.userError "original generalized program profile rejected")
      | some profiles => pure ⟨original, originals, cached, profiles⟩
    else throw (IO.userError "original generalized full cache changed")
  else throw (IO.userError "original generalized source count changed")

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

theorem ProfiledFixture.body (fixture : ProfiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.original.recipe.compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.original.recipe.compiled
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.original.recipe.compiled.indexed.layouts}
    (member : entry ∈ fixture.original.recipe.compiled.indexed.entries) :
    Nonempty (CellAwareLexicalNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial fixture.original.recipe.compiled.compatible.checked) header)
      header.context header.function.resultType) := by
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  exact CellAwareLexicalNamedBodyReceipt.of_header prepared aligned fixture.ready wellFormed member
    (profile.for_compilation prepared.compilation)

def checkProgramProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "INTERLEAVED_LOCAL_COMPLETE_STATIC_INVENTORY: originals1/cache1/profile1"

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
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

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalTrace
/-! Independent Source execution of the original identity body after a genuine
local-scheme instance has been selected. No target execution is a premise.
Closures capture by value: the generalized `let` copies the function's
environment once, and each instance call copies the descriptor's captures
again before allocating its parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

/-- The exact materialized body copies the descriptor's captures, reads its
newly allocated parameter and returns it. The supplied frame is static Source
code/evidence validity. -/
theorem Shape.identity_applies {source : TypedSource} (shape : Shape source)
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
theorem Shape.invoke {source : TypedSource} (shape : Shape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
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
theorem Shape.instance {source : TypedSource} (shape : Shape source)
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
theorem Shape.frame {source : TypedSource} (shape : Shape source)
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

/-- The heap after the generalized `let`: the copies of the function's
environment, then the principal descriptor over those copies. -/
def Shape.declaredHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  shape.allocatedHeap context (copies source environment before).1 (copies source environment before).2

/-- The Word call copies the descriptor's captures, then allocates its
parameter. -/
def Shape.wordHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source (copies source environment before).1 (shape.declaredHeap context environment before)).2.cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

def Shape.valueHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.wordHeap context environment before).cells ++
    [{type := shape.valueBinder.scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

/-- The Bool call copies the same captures again, after the ordinary local,
then allocates its parameter. -/
def Shape.finalHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨(copies source (copies source environment before).1 (shape.valueHeap context environment before)).2.cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .bool)]).scheme.body, value := some (.bool flag)}]⟩

/-- Full independent body trace: the environment copies and principal
descriptor allocation, Word copies and call, ordinary allocation of its
result, Bool copies and call, then ordered product return. All frame premises
are static code/evidence validity, and no native result is used. -/
theorem Shape.body_trace {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext finalContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool)
    (unique : NodeOccurrencesUnique source)
    (different : shape.binder.id ≠ shape.flag.id)
    (extended : BinderExtends source.owner context shape.binder nextContext)
    (valueExtended : BinderExtends source.owner nextContext shape.valueBinder finalContext)
    (valueDifferent : shape.valueBinder.id ≠ shape.binder.id)
    (flagDifferent : shape.valueBinder.id ≠ shape.flag.id)
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (finalFields : Dynamic.RuntimeContextFields context finalContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (word : TypeWellFormed nextContext .word)
    (finalScheme : SchemeWellFormed finalContext shape.binder.scheme)
    (boolean : TypeWellFormed finalContext .bool)
    {literalType : TypeSystem.Ty}
    (literal : ExpressionHasType source nextContext shape.literal.node.id literalType)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (flagLookup : Dynamic.Environment.LooksUp environment shape.flag.id location)
    (flagRead : Dynamic.Heap.Reads before location cell)
    (flagDescriptor : cell.generalized = none) (flagValue : cell.value = some (.bool flag))
    (readable : Readable before environment)
    (wordFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context (copies source environment before).1).instantiate [(shape.typeVariable, .word)]
        (evidence.applySubstitution [(shape.typeVariable, .word)])))
    (boolFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context (copies source environment before).1).instantiate [(shape.typeVariable, .bool)]
        (evidence.applySubstitution [(shape.typeVariable, .bool)]))) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.returned.id] finalContext
      (.returned (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap context environment before flag) := by
  let captured := (copies source environment before).1
  let middle := (copies source environment before).2
  have snapshot : Dynamic.EnvironmentCopies source environment before captured middle :=
    copies_spec source readable
  let allocated := shape.declaredHeap context environment before
  let wordCopied := (copies source captured allocated).2
  let first := shape.wordHeap context environment before
  let bound := shape.valueHeap context environment before
  let after := shape.finalHeap context environment before flag
  let locals := (shape.binder.id, ⟨middle.cells.length⟩) :: environment
  have allocation : Dynamic.Heap.AllocatesGeneralized middle (shape.descriptor context captured)
      ⟨middle.cells.length⟩ allocated := .append
  have capturedAllocated : Readable allocated captured :=
    (Readable.of_copies snapshot readable).mono (Dynamic.HeapMetadataExtend.of_generalized_allocation allocation)
  have wordCopy := copies_spec_applySubstitution [(shape.typeVariable, .word)] source capturedAllocated
  have firstAllocation : Dynamic.Heap.Allocates wordCopied
      (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body
      (some (.word (Core.Word.ofNatModulo 11))) ⟨wordCopied.cells.length⟩ first := .append
  have literalTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals
      allocated shape.literal.node.id (.word (Core.Word.ofNatModulo 11)) allocated := by
    simpa only [shape.literalValue] using shape.literal.evaluates evidence locals allocated unique literal
  have firstTrace := shape.invoke shape.wordCall captured locals [(shape.typeVariable, .word)] evidence []
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl fields
    (shape.instance evidence wellformed word) wordFrame literalTrace wordCopy
  have valueAllocation : Dynamic.Heap.Allocates first shape.valueBinder.scheme.body
      (some (.word (Core.Word.ofNatModulo 11))) ⟨first.cells.length⟩ bound := .append
  let valueLocals := (shape.valueBinder.id, ⟨first.cells.length⟩) :: locals
  have initialized : Dynamic.StatementExecutes program nextContext evidence source locals allocated shape.valueInitialized.id
      finalContext (.fallthrough valueLocals) bound :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm firstTrace
      (by rw [shape.valueScheme]; rfl) valueExtended valueAllocation
  have valueTrace : Dynamic.ExpressionEvaluates program finalContext evidence source valueLocals bound
      shape.valueRead.node.id (.word (Core.Word.ofNatModulo 11)) bound := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.valueRead.found)
    · rw [shape.valueRead.form]
      exact .local (by rw [shape.valueRead.requirements, shape.valueRead.coercions]; rfl)
        .head valueAllocation.reads_new rfl rfl
    · rw [shape.valueRead.coercions]; exact .nil
  have flagTrace : Dynamic.ExpressionEvaluates program finalContext evidence source valueLocals bound
      shape.flagRead.node.id (.bool flag) bound := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.flagRead.found)
    · rw [shape.flagRead.form]
      exact .local (by rw [shape.flagRead.requirements, shape.flagRead.coercions]; rfl)
        (.tail flagDifferent (.tail different flagLookup))
        (valueAllocation.preserves_read (firstAllocation.preserves_read (wordCopy.preserves_read
          (allocation.preserves_read (snapshot.preserves_read flagRead)))))
        flagDescriptor flagValue
    · rw [shape.flagRead.coercions]; exact .nil
  have capturedBound : Readable bound captured :=
    ((capturedAllocated.mono wordCopy.metadata_extends).mono
      (Dynamic.HeapMetadataExtend.of_allocation firstAllocation)).mono
      (Dynamic.HeapMetadataExtend.of_allocation valueAllocation)
  have boolCopy := copies_spec_applySubstitution [(shape.typeVariable, .bool)] source capturedBound
  have secondTrace := shape.invoke shape.boolCall captured valueLocals [(shape.typeVariable, .bool)] evidence []
    (.tail valueDifferent .head)
    (valueAllocation.preserves_read (firstAllocation.preserves_read
      (wordCopy.preserves_read allocation.reads_new))) rfl finalFields
    (shape.instance evidence finalScheme boolean) boolFrame flagTrace boolCopy
  have tupleTrace : Dynamic.ExpressionEvaluates program finalContext evidence source valueLocals bound
      shape.tuple.id (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
    · rw [shape.tupleForm]
      exact .tuple (by rw [shape.tupleRequirements, shape.tupleCoercions]; rfl)
        (.cons valueTrace (.cons secondTrace .nil)) (.cons (.singleton _))
    · rw [shape.tupleCoercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.cons (shape.initializes evidence snapshot extended)
  apply Dynamic.FunctionStatementsExecute.cons initialized
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTrace

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalSourceFirst
/-! Original checker typing supplies both materialized closure frames before
the independent Source execution. No completed native call is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem lookup_declared {heap : Dynamic.Heap} {scope : Resolved.LocalScope TypeSystem.Scheme}
    {environment : Dynamic.Environment} (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment id location) : id ∈ scope.map Prod.fst := by
  induction agrees with
  | nil => cases lookup
  | cons _ _ _ _ ih =>
    cases lookup with
    | head => simp
    | tail _ tail => exact List.mem_cons_of_mem _ (ih tail)

private theorem Shape.literal_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.wordCall.node.id type) :
    ∃ literalType, ExpressionHasType source context shape.literal.node.id literalType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.wordCall.found)
    rw [shape.wordCall.form] at raw
    cases raw with
    | indirectCall _ arguments _ =>
      cases arguments with
      | cons literal _ => exact ⟨_, literal⟩

/-- The actual generalized declaration rule derives both Word and Bool code
frames from the copies of the lexical environment and the original typed body. -/
theorem Shape.body_from_source {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {control : ControlContext} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typed : StatementsHaveType source control context
      [shape.initialized.id, shape.valueInitialized.id, shape.returned.id] final facts)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (flagLookup : Dynamic.Environment.LooksUp environment shape.flag.id location)
    (flagRead : Dynamic.Heap.Reads before location cell)
    (flagDescriptor : cell.generalized = none) (flagValue : cell.value = some (.bool flag)) :
    ∃ nextContext, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.returned.id] nextContext
      (.returned (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap context environment before flag) := by
  have unique := runtime.graph.nodeOccurrencesUnique
  obtain ⟨next, _, _, first, rest⟩ := head_tail typed
  have original := form_at unique shape.initializedFound first
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ =>
    rw [shape.scheme] at monomorphic
    cases monomorphic
  | letInitializedGeneralized polymorphic requirements generalizes initializer extended =>
    have readable := Readable.of_agrees locals
    have snapshot := copies_spec source readable
    have descriptorTyped := (shape.captures context (copies source environment before).1).wellTyped runtime
      (snapshot.agrees locals) polymorphic requirements generalizes initializer extended
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    obtain ⟨valueContext, _, _, valueStatement, _rest⟩ := head_tail rest
    have originalValue := form_at unique shape.valueFound valueStatement
    rw [shape.valueForm] at originalValue
    cases originalValue with
    | letInitializedGeneralized impossible _ _ _ _ =>
      exact False.elim (impossible (by rw [shape.valueScheme]; rfl))
    | letInitialized valueTyped _ valueExtended =>
      obtain ⟨literalType, literal⟩ := shape.literal_typed unique valueTyped
      have valueFields := Dynamic.RuntimeContextFields.ofBinderExtends valueExtended
      cases extended with
      | intro wellformed fresh =>
        have scheme : SchemeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
            shape.binder.scheme := {
          binders := wellformed.scheme.binders.withLocal _ _ _
          quantified_nodup := wellformed.scheme.quantified_nodup
          body := wellformed.scheme.body.withLocal _ _ _
        }
        have word : TypeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .word :=
          ⟨scheme.binders, .builtin .word⟩
        have boolean : TypeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .bool :=
          ⟨scheme.binders, .builtin .bool⟩
        have descriptorNext : Dynamic.GeneralizedClosureWellTyped
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
            (copies source environment before).2 (shape.descriptor context (copies source environment before).1) :=
          ⟨descriptorTyped.same_signatures, descriptorTyped.code, descriptorTyped.captures⟩
        have different : shape.binder.id ≠ shape.flag.id := by
          intro same
          exact fresh.1 (same.symm ▸ lookup_declared locals flagLookup)
        cases valueExtended with
        | intro valueWellformed valueFresh =>
          have valueDifferent : shape.valueBinder.id ≠ shape.binder.id := by
            intro same
            apply valueFresh.1
            simp only [Context.withLocal, List.map_cons]
            exact same.symm ▸ List.mem_cons_self
          have flagDifferent : shape.valueBinder.id ≠ shape.flag.id := by
            intro same
            apply valueFresh.1
            exact List.mem_cons_of_mem _ (same.symm ▸ lookup_declared locals flagLookup)
          have finalScheme : SchemeWellFormed
              ((context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements).withLocal
                shape.valueBinder.id shape.valueBinder.scheme shape.valueBinder.schemeRequirements) shape.binder.scheme := {
            binders := scheme.binders.withLocal _ _ _
            quantified_nodup := scheme.quantified_nodup
            body := scheme.body.withLocal _ _ _
          }
          exact ⟨_, shape.body_trace evidence environment before flag unique different
            (.intro wellformed fresh) (.intro valueWellformed valueFresh) valueDifferent flagDifferent fields
            (fields.trans valueFields) scheme word finalScheme ⟨finalScheme.binders, .builtin .bool⟩
            literal flagLookup flagRead flagDescriptor flagValue readable
            (shape.frame _ _ evidence catalog descriptorNext fields runtime.signatures
              (fields.covers covers) scheme word)
            (shape.frame _ _ evidence catalog descriptorNext fields runtime.signatures
              (fields.covers covers) scheme boolean)⟩

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
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
    selected.packet.header.function.body = [shape.initialized.id, shape.valueInitialized.id, shape.returned.id] :=
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
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.word (Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap selected.packet.header.context (flagEnvironment shape.flag before)
        (flagHeap before flag) flag) := by
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
  have catalog : SignatureCatalogWellFormed header.context.signatures :=
    runtime.signatures.symm ▸ wellFormed.signatures
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (flagEnvironment shape.flag before) (flagHeap before flag) flag runtime catalog covers locals typed
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl rfl
  exact ⟨bound, next, selected.statements shape ▸ body⟩

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalTyping
/-! The actual original generalized identity body receives independent
declarative typing, including its principal initializer and both instances.
The observer checks finite metadata and constructs every typing rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

def resultType : TypeSystem.Ty := .product .word .bool

def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}

def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}

def bodyFacts : BodyFacts := .cons localFacts (.cons localFacts (.singleton (returnFacts resultType)))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext bodyFacts
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
  have same : statements = certificate.statements := roots_injective_variant (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨bodyFacts, ?_, ?_⟩
  · rw [certificate.result]; rfl
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

private def originalCall {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type : TypeSystem.Ty}
    (shape : CallShape source binder argument type) :
    Tests.SourceCoreSelectedGeneralizedLocal.CallShape source binder argument type :=
  ⟨shape.callee, shape.node, shape.metadata, shape.found, shape.form, shape.arity,
    shape.argumentCoercions, shape.requirements, shape.coercions⟩

private def originalWord {source : TypedSource} (shape : WordNode source) :
    Tests.SourceCoreSelectedGeneralizedLocal.WordNode source :=
  ⟨shape.node, shape.literal, shape.resolution, shape.found, shape.form, shape.target,
    shape.requirements, shape.coercions⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeShape function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "generalized original signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType)
    "generalized original signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
  let ⟨flagExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.flag
  let ⟨flagRequirements⟩ ← observe (shape.flag.schemeRequirements = []) "generalized input requirements"
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]
    exact .cons shape.flagScheme flagExtended (.nil _)
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨parameterExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder principal function.typedBody.owner shape.parameter
  let ⟨parameterTyped⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.parameterRead parameterContext
    parameterExtended.local_self parameterExtended.local_scheme_requirements_self
  let ⟨identityType⟩ ← observe (shape.identityReturn.type = .variable shape.typeVariable)
    "generalized original identity return type"
  have identity : StatementHasType function.typedBody {returnType := .variable shape.typeVariable}
      parameterContext shape.identityReturn.id parameterContext (returnFacts (.variable shape.typeVariable)) :=
    .returnValue (lookupStatement?_sound shape.identityFound) shape.identityForm parameterTyped identityType
  have parameterInputs : MonoBindersExtend function.typedBody.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme parameterExtended (.nil _)
  have lambdaForm : ExpressionFormHasRawType function.typedBody principal shape.lambda.form
      (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameterInputs (.singleton identity) (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨initializerTyped⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) shape.lambdaFound lambdaForm
  let generalizedContext := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  let ⟨localExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder lexical function.typedBody.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨initializedType⟩ ← observe (shape.initialized.type = .unit) "generalized original let type"
  have initialized : StatementHasType function.typedBody {returnType := resultType} lexical
      shape.initialized.id generalizedContext localFacts := by
    refine .letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
      generalized ?_ localExtended initializedType
    simpa only [shape.scheme] using initializerTyped
  let ⟨wordRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.wordCall.callee generalizedContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨literalTyped⟩ ← word (originalWord shape.literal) generalizedContext
  let ⟨wordCall⟩ ← call (originalCall shape.wordCall) generalizedContext wordRead literalTyped
  let finalContext := generalizedContext.withLocal shape.valueBinder.id shape.valueBinder.scheme shape.valueBinder.schemeRequirements
  let ⟨valueExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder generalizedContext function.typedBody.owner shape.valueBinder
  let ⟨valueType⟩ ← observe (shape.valueInitialized.type = .unit) "interleaved ordinary initialized type"
  let valueGeneralizes : PLift (SchemeGeneralizes generalizedContext shape.valueBinder.scheme) ←
    match accepted : validateSchemeGeneralizes generalizedContext shape.valueBinder.scheme with
    | .error _ => throw (IO.userError "interleaved exact ordinary generalization")
    | .ok () => pure ⟨validateSchemeGeneralizes_success accepted⟩
  have valueInitialized : StatementHasType function.typedBody {returnType := resultType} generalizedContext
      shape.valueInitialized.id finalContext localFacts :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm
      (by simpa only [shape.valueScheme, originalCall, TypeSystem.Scheme.mono] using wordCall)
      (by rw [shape.valueScheme]; rfl) valueGeneralizes.down valueExtended valueType
  let ⟨different⟩ ← observe (shape.binder.id ≠ shape.flag.id) "interleaved distinct input and generalized local"
  let ⟨valueDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.binder.id) "interleaved distinct local binders"
  let ⟨flagDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.flag.id) "interleaved distinct input and ordinary local"
  let ⟨boolRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.boolCall.callee finalContext
    (.tail valueDifferent localExtended.local_self) (.tail valueDifferent localExtended.local_scheme_requirements_self)
  let ⟨flagRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.flagRead finalContext
    (.tail flagDifferent (.tail different flagExtended.local_self))
    (.tail flagDifferent (.tail different flagExtended.local_scheme_requirements_self))
  let ⟨valueRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.valueRead finalContext
    valueExtended.local_self valueExtended.local_scheme_requirements_self
  let ⟨boolCall⟩ ← call (originalCall shape.boolCall) finalContext boolRead flagRead
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]
    exact .tuple (.cons valueRead (.cons boolCall (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "generalized original return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return {
    statements := [shape.initialized.id, shape.valueInitialized.id, shape.returned.id]
    roots := shape.roots
    context := lexical
    finalContext := finalContext
    inputs := inputs
    typed := .cons initialized (.cons valueInitialized (.singleton returned))
    result := result }

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
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
      "generalized full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "generalized original signature membership")
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
  | _ => throw (IO.userError "generalized original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized original complete cache size")
  IO.println "INTERLEAVED_LOCAL_ORIGINAL_TYPING: originals1/cache1"
  IO.println "INTERLEAVED_LOCAL_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedInterleavedLocal
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


end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedInterleavedLocal
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

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
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
    (.product (.word (Word.ofNatModulo 11)) (.bool flag))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag) flag)

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
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicLexicalForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

/-- The complete original inventory is produced from its actual declarative
proof before the public call is resumed. -/
theorem complete_from_source (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    ∃ selected : SelectedInventory fixture row, Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
  exact ⟨selected, initial_from_source selected shape flag typing started callableProfile⟩

def publicProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "interleaved actual callable profile"
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    let _proof := complete_from_source fixture row shape flag typing started profile
    match ← started.call.checkpoint.resume runOptions.executionFuel runOptions.outputValidationFuel with
    | .succeeded returned =>
      unless returned.value == .product (.word (Word.ofNatModulo 11)) (.bool flag) do
        throw (IO.userError "interleaved Source-first public result")
    | _ => throw (IO.userError "interleaved Source-first public call failed")
  IO.println "INTERLEAVED_LOCAL_SOURCE_PUBLIC: originals1/cache1/typing1/profile1"
  IO.println "INTERLEAVED_LOCAL_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreSelectedInterleavedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedInterleavedLocalCompleteOutcome
/-! The unchanged interleaved Source program produces a complete public outcome
receipt before resume. Its alternative stage stop includes the actual failed
session and reached mixed history. This fixture executes the success branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedInterleavedLocal.FailureBridge
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {fixture : ProfiledFixture} {row : Row fixture.original}

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicLexicalFailureForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.word (Word.ofNatModulo 11)) (.bool flag))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag) flag)

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
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicLexicalFailureForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

/-- The complete original inventory is produced from its actual declarative
proof before the public call is resumed. -/
theorem complete_from_source (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    ∃ selected : SelectedInventory fixture row, Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
  exact ⟨selected, initial_from_source selected shape flag typing started callableProfile⟩

def publicProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "interleaved actual callable profile"
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    let _proof := complete_from_source fixture row shape flag typing started profile
    match ← started.call.checkpoint.resume runOptions.executionFuel runOptions.outputValidationFuel with
    | .succeeded returned =>
      unless returned.value == .product (.word (Word.ofNatModulo 11)) (.bool flag) do
        throw (IO.userError "interleaved Source-first public result")
    | _ => throw (IO.userError "interleaved Source-first public call failed")
  IO.println "INTERLEAVED_LOCAL_COMPLETE_OUTCOME: originals1/cache1/typing1/profile1"
  IO.println "INTERLEAVED_LOCAL_COMPLETE_OUTCOME_PASS"

end Tests.SourceCoreSelectedInterleavedLocal.FailureBridge
end
