import Solcore.Test.SourceCoreSelectedFaultingLocalSource
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedBodyProducer
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
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
       .statement absentDeclared,.expression absentNode,.expression flagNode,.expression boolCallee,.expression second,
       .expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "generalized original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "generalized original binder")
  let .lambda [parameter] (.variable typeVariable) _ := lambda.form
    | throw (IO.userError "generalized principal lambda")
  let .letDecl valueBinder _ := valueInitialized.form | throw (IO.userError "interleaved ordinary binder")
  let .letDecl absentBinder none := absentDeclared.form | throw (IO.userError "faulting absent binder")
  let absentRead ← Tests.SourceCoreNamedBranch.observeRead source absentBinder absentNode .word
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
  let ⟨absentScheme⟩ ← observed (absentBinder.scheme = .mono .word) "faulting absent scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement valueInitialized.id,.statement absentDeclared.id,.statement returned.id]) "generalized original root order"
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
  let ⟨absentFound⟩ ← observed (source.lookupStatement? absentDeclared.id = some absentDeclared) "faulting absent lookup"
  let ⟨absentForm⟩ ← observed (absentDeclared.form = .letDecl absentBinder none) "faulting absent declaration"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "generalized tuple lookup"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [absentRead.node.id,boolCall.node.id]) "generalized ordered calls"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "generalized tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "generalized tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "generalized outer return lookup"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "generalized outer return form"
  return ⟨flag,binder,parameter,typeVariable,initialized,lambda,identityReturn,parameterRead,literal,flagRead,
    wordCall,boolCall,valueBinder,valueInitialized,absentBinder,absentDeclared,absentRead,tuple,returned,inputs,flagScheme,scheme,schemeRequirements,parameterScheme,
    parameterRequirements,valueScheme,absentScheme,roots,initializedFound,initializedForm,lambdaFound,lambdaForm,lambdaRaw,
    lambdaType,lambdaRequirements,lambdaCoercions,identityFound,identityForm,literalValue,
    valueFound,valueForm,absentFound,absentForm,tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩


end Tests.SourceCoreSelectedFaultingLocal
