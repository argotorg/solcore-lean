import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Index
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Nested formation tests

Nested closure formation through the closure family and public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev DirectCall := Tests.SourceCoreRecursiveIndex.DirectCall
abbrev IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :=
  Tests.SourceCoreRecursiveIndex.IdentityShape function signature .word
abbrev closureType : TypeSystem.Ty := .function .unit .word
abbrev outerType : TypeSystem.Ty := .function .unit closureType
private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)
private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]


structure FactoryShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody identity initialRead.node.id .word .word
  read : Read function.typedBody localBinder .word
  call : DirectCall function.typedBody identity read.node.id .word .word
  initialized : StatementNode
  innerReturn : StatementNode
  expression : ExpressionNode
  outerReturn : StatementNode
  outerExpression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [outerType]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  localOrdinary : localBinder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some initial.value.node.id)
  initializedType : initialized.type = .unit
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some call.value.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = closureType
  expressionType : expression.type = closureType
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  outerReturnFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some expression.id)
  outerReturnType : outerReturn.type = closureType
  outerExpressionFound : function.typedBody.lookupExpression? outerExpression.id = some outerExpression
  outerLambda : outerExpression.form = .lambda [] closureType [initialized.id, outerReturn.id]
  outerExpressionRaw : outerExpression.rawType = outerType
  outerExpressionType : outerExpression.type = outerType
  outerRequirements : outerExpression.requirements = []
  outerCoercions : outerExpression.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  returnStatement : statement.form = .returnStmt (some outerExpression.id)
  statementType : statement.type = outerType

def FactoryShape.nodeList {function signature identity} (shape : FactoryShape function signature identity) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
   .statement shape.initialized, .expression shape.read.node, .expression shape.call.callee.node, .expression shape.call.value.node,
   .statement shape.innerReturn, .expression shape.expression, .statement shape.outerReturn,
   .expression shape.outerExpression, .statement shape.statement]

theorem FactoryShape.statementTyping {function signature identity}
    (shape : FactoryShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  let returned : StatementFacts := {type:=outerType, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.singleton returned, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    let locals := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.localOwner
          scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
          quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.localRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localDistinct]
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have initial := shape.initial.typed (fields ▸ identityMember) word initialRead
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed shape.localScheme shape.localRequirements localWord
      localExtended.local_self localExtended.local_scheme_requirements_self
    have called := shape.call.typed (show identity ∈ locals.signatures.functions from fields ▸ identityMember) localWord read
    have callable : TypeAdmissible locals closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have expressionTyped : ExpressionHasType function.typedBody locals shape.expression.id closureType := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm called shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initialized : StatementHasType function.typedBody ⟨closureType,0⟩ lexical shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    have outerCallable : TypeAdmissible lexical outerType :=
      ⟨binders, .function (.builtin .unit) (.function (.builtin .unit) (.builtin .word))⟩
    have outerTyped : ExpressionHasType function.typedBody lexical shape.outerExpression.id outerType := by
      rw [← shape.outerExpressionType]
      refine .intro (lookupExpression?_sound shape.outerExpressionFound)
        (shape.outerLambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.cons initialized (.singleton (.returnValue (lookupStatement?_sound shape.outerReturnFound)
            shape.outerReturnForm expressionTyped shape.outerReturnType)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.outerExpressionRaw
        outerCallable (shape.outerExpressionType ▸ outerCallable) ?_
      rw [shape.outerRequirements, shape.outerCoercions, shape.outerExpressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement outerTyped shape.statementType)⟩

def observeFactory (function : CheckedFunction) (signature identity : ProgramFunctionSignature) : IO (FactoryShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "make inputs")
  let [.expression initialReadNode, .expression initialCallee, .expression initialValue, .statement initialized, .expression readNode, .expression callee, .expression value, .statement innerReturn, .expression expression, .statement outerReturn, .expression outerExpression, .statement statement] := function.typedBody.nodes | throw (IO.userError "make nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "make local")



  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder initialReadNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity initialRead.node.id initialCallee initialValue .word .word
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder readNode .word
  let call ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity read.node.id callee value .word .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "formation parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "formation inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [outerType]) "formation returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "formation inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "formation binderRequirements"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "formation localScheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "formation localRequirements"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "formation localOwner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "formation localDistinct"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "formation localOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "formation roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "formation initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initial.value.node.id)) "formation initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "formation initializedType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "formation innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some call.value.node.id)) "formation innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "formation innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "formation expressionFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "formation lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType) "formation expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = closureType) "formation expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "formation requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "formation coercions"
  let ⟨outerReturnFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "nested outerReturnFound"
  let ⟨outerReturnForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.id)) "nested outerReturnForm"
  let ⟨outerReturnType⟩ ← observed (outerReturn.type = closureType) "nested outerReturnType"
  let ⟨outerExpressionFound⟩ ← observed (function.typedBody.lookupExpression? outerExpression.id = some outerExpression) "nested outerExpressionFound"
  let ⟨outerLambda⟩ ← observed (outerExpression.form = .lambda [] closureType [initialized.id, outerReturn.id]) "nested outerLambda"
  let ⟨outerExpressionRaw⟩ ← observed (outerExpression.rawType = outerType) "nested outerExpressionRaw"
  let ⟨outerExpressionType⟩ ← observed (outerExpression.type = outerType) "nested outerExpressionType"
  let ⟨outerRequirements⟩ ← observed (outerExpression.requirements = []) "nested outerRequirements"
  let ⟨outerCoercions⟩ ← observed (outerExpression.coercions = []) "nested outerCoercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "formation statementFound"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some outerExpression.id)) "formation returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = outerType) "formation statementType"
  return {binder, localBinder, initialRead, initial, read, call, initialized, innerReturn, expression, outerReturn, outerExpression, statement, parameters, inputTypes, returns, inputs, binderRequirements, localScheme, localRequirements, localOwner, localDistinct, localOrdinary, roots, initializedFound, initializedForm, initializedType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, lambda, expressionRaw, expressionType, requirements, coercions, outerReturnFound, outerReturnForm, outerReturnType, outerExpressionFound, outerLambda, outerExpressionRaw, outerExpressionType, outerRequirements, outerCoercions, statementFound, returnStatement, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function make(seed: Word) returns (function() returns (function() returns (Word))) { return lam() { let saved: Word = identity(seed); return lam() { return identity(saved); }; }; }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  makeFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  makeSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, makeFunction]
  signatures : program.signatures.functions = [identitySignature, makeSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  makeShape : FactoryShape makeFunction makeSignature identitySignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, makeFunction], [identitySignature, makeSignature] =>
      let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityFunction identitySignature .word
      let makeShape ← observeFactory makeFunction makeSignature identitySignature
      let ⟨methods⟩ ← observed (program.methods = []) "direct fixture methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "direct fixture identityDeclaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "direct fixture makeDeclaration"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "direct fixture identityMake"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "direct fixture identityNodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "direct fixture makeNodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
          · exact identityShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program := program
        checked := checked
        wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction := identityFunction
        makeFunction := makeFunction
        identitySignature := identitySignature
        makeSignature := makeSignature
        functions := functions
        signatures := signatures
        methods := methods
        identityDeclaration := identityDeclaration
        makeDeclaration := makeDeclaration
        identityMake := identityMake
        identityShape := identityShape
        makeShape := makeShape
        identityNodes := identityNodes
        makeNodes := makeNodes
      }
    | _, _ => throw (IO.userError "direct fixture declaration count")

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let seeds := [SourceCompiler.Seed.declaration checked.identitySignature.id,
    SourceCompiler.Seed.declaration checked.makeSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedMetadata.instantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩



/-- Each observation refers to an actual compiler row, unique physical slot,
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  assumptions : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨assumptions⟩ ← observed (row.assumptions = []) "direct row assumptions"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          assumptions := assumptions
          ordinary := ordinary
          inputsOrdinary := by
            intro binder member
            have selected := List.all_eq_true.mp ordinaryInputs binder member
            cases same : binder.comptime <;> simp_all
          target := target
          global := global
          index := index
          slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
          globalKey := globalKey
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

structure ObservedProgram (fixture : CompiledFixture) where
  identityRow : ObservedRow fixture fixture.identitySignature
  makeRow : ObservedRow fixture fixture.makeSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 2
  identityMake : identityRow.index ≠ makeRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature fixture.identitySignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  makeNodes : makeRow.row.function.typedBody.nodes = makeShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let makeRow ← observeRow fixture fixture.makeSignature
  let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityRow.row.function fixture.identitySignature .word
  let makeShape ← observeFactory makeRow.row.function fixture.makeSignature fixture.identitySignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 2) "direct compiled globalsLength"
  let ⟨identityMake⟩ ← observed (identityRow.index ≠ makeRow.index) "direct compiled identityMake"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "direct compiled identityNodes"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = makeShape.nodeList) "direct compiled makeNodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "direct compiled noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "direct compiled profile"
  return {identityRow, makeRow, identityShape, makeShape, globalsLength, identityMake, identityNodes, makeNodes, noLocals, profile}

/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- Both real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (identityInput makeInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ makeInput.row = observed.makeRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (makeHeader : ActualHeader fixture observed.makeRow.row),
        identityHeader.header = identityPacket.header ∧ makeHeader.header = makePacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons identityPacket (.cons makePacket .nil))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  refine ⟨identityInput, makeInput, identityRow, makeRow,
    identityPacket, makePacket, identityHeader, makeHeader, identityEq, makeEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index := by
    have distinct := observed.identityMake
    omega
  rcases casesIndex with same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .tail _ (.head _)
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)

structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")


theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.identityRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.identityNodes, Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.identityShape.read.form] at form; cases form
  · cases same

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationIdentitySupport
/-! The actual identity row is a compiler-produced read body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem identity_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.identityRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.identityShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.identityNodes] at present
  simpa only [Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.identity_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [identity_expression observed found, observed.identityShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.identityShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.identity_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.identityShape.read.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.identity_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.identity_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.identity_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.identityShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.identityShape.read.node.id
    observed.identityShape.statement observed.identityShape.roots observed.identityShape.statementFound observed.identityShape.statementForm
  exact ⟨terminal, expression, ActualHeader.identity_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ObservedProgram.make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.initialRead.node ∨ node = observed.makeShape.initial.callee.node ∨ node = observed.makeShape.initial.value.node ∨ node = observed.makeShape.read.node ∨ node = observed.makeShape.call.callee.node ∨ node = observed.makeShape.call.value.node ∨ node = observed.makeShape.expression ∨ node = observed.makeShape.outerExpression := by
  have present := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.make_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.makeRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.requirements
    · exact observed.makeShape.initial.callee.requirements
    · exact observed.makeShape.initial.value.requirements
    · exact observed.makeShape.read.requirements
    · exact observed.makeShape.call.callee.requirements
    · exact observed.makeShape.call.value.requirements
    · exact observed.makeShape.requirements
    · exact observed.makeShape.outerRequirements
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.coercions
    · exact observed.makeShape.initial.callee.coercions
    · exact observed.makeShape.initial.value.coercions
    · exact observed.makeShape.read.coercions
    · exact observed.makeShape.call.callee.coercions
    · exact observed.makeShape.call.value.coercions
    · exact observed.makeShape.coercions
    · exact observed.makeShape.outerCoercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.initialRead.form] at form; cases form
    · rw [observed.makeShape.initial.calleeForm] at form; cases form
    · rw [observed.makeShape.initial.form] at form; cases form
    · rw [observed.makeShape.read.form] at form; cases form
    · rw [observed.makeShape.call.calleeForm] at form; cases form
    · rw [observed.makeShape.call.form] at form; cases form
    · rw [observed.makeShape.lambda] at form; cases form
    · rw [observed.makeShape.outerLambda] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem DirectCall.syntax {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {parameter result : TypeSystem.Ty}
    (call : DirectCall source signature argument parameter result)
    (child : GeneralSyntax source argument) : GeneralSyntax source call.value.node.id := by
  refine .direct call.value.found call.form ?_ ?_
  · rw [call.exact]; exact ⟨rfl, rfl⟩
  · intro id member
    cases List.mem_singleton.mp member
    exact child

theorem ObservedProgram.make_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.call.value.node.id :=
  observed.makeShape.call.syntax (.leaf (.read observed.makeShape.read.found observed.makeShape.read.form))

theorem ObservedProgram.make_initial_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.initial.value.node.id :=
  observed.makeShape.initial.syntax (.leaf (.read observed.makeShape.initialRead.found observed.makeShape.initialRead.form))

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .function handle => return ⟨call, handle, returned⟩
  | _ => throw (IO.userError "captured reuse expected a function export")

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


structure ObservedFormation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (parent : SourceCorePublicValues.Handle)
    extends ObservedInvocation session parent .unit where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFormation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (parent : SourceCorePublicValues.Handle) :
    IO (ObservedFormation session parent) := do
  let call ← observeInvocation session parent .unit
  match returned : call.completion.value with
  | .function handle => pure ⟨call, handle, returned⟩
  | _ => throw (IO.userError "nested formation expected inner function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  firstFormation : ObservedFormation first.completion.session first.handle
  second : ObservedFunctionCall firstFormation.completion.session observed.makeRow.row.key [.word secondSeed]
  secondFormation : ObservedFormation second.completion.session second.handle
  distinctOuter : first.handle ≠ second.handle
  distinctInner : firstFormation.handle ≠ secondFormation.handle
  firstRead : ObservedInvocation secondFormation.completion.session firstFormation.handle .unit
  firstValue : firstRead.completion.value = .word seed
  secondRead : ObservedInvocation firstRead.completion.session secondFormation.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session firstFormation.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let firstFormation ← observeFormation first.completion.session first.handle
  let second ← observeFunctionCall firstFormation.completion.session observed.makeRow.row.key [.word secondSeed]
  let secondFormation ← observeFormation second.completion.session second.handle
  if distinctOuter : first.handle ≠ second.handle then
    if distinctInner : firstFormation.handle ≠ secondFormation.handle then
      let firstRead ← observeInvocation secondFormation.completion.session firstFormation.handle .unit
      if firstValue : firstRead.completion.value = .word seed then
        let secondRead ← observeInvocation firstRead.completion.session secondFormation.handle .unit
        if secondValue : secondRead.completion.value = .word secondSeed then
          let repeatedRead ← observeInvocation secondRead.completion.session firstFormation.handle .unit
          if repeatedValue : repeatedRead.completion.value = .word seed then
            return {
              first := first
              firstFormation := firstFormation
              second := second
              secondFormation := secondFormation
              distinctOuter := distinctOuter
              distinctInner := distinctInner
              firstRead := firstRead
              firstValue := firstValue
              secondRead := secondRead
              secondValue := secondValue
              repeatedRead := repeatedRead
              repeatedValue := repeatedValue
            }
          else throw (IO.userError "retained first inner capture changed")
        else throw (IO.userError "second inner capture not20")
      else throw (IO.userError "first inner capture not10")
    else throw (IO.userError "nested formation lost distinct inner captures")
  else throw (IO.userError "nested formation lost distinct outer captures")

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original


theorem ObservedProgram.make_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.localBinder.id = .ok observed.makeShape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, observed.makeShape.initialRead.form,
    observed.makeShape.initial.calleeForm, observed.makeShape.initial.form,
    observed.makeShape.read.form, observed.makeShape.call.calleeForm, observed.makeShape.call.form,
    observed.makeShape.initializedForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda,
    observed.makeShape.returnStatement, observed.makeShape.outerLambda, observed.makeShape.outerReturnForm, observed.makeShape.localOwner, Ne.symm observed.makeShape.localDistinct,
    observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.localRequirements]

theorem ObservedProgram.outer_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.makeRow.row.function.typedBody true
      [observed.makeShape.initialized.id, observed.makeShape.outerReturn.id] :=
  .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
    (.returnValue [] observed.makeShape.outerReturnFound observed.makeShape.outerReturnForm)

theorem ObservedProgram.outer_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (unique : NodeOccurrencesUnique observed.makeRow.row.function.typedBody)
    {approved : ExpressionId → Prop} (initial : approved observed.makeShape.initial.value.node.id)
    (formation : approved observed.makeShape.expression.id)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType observed.makeRow.row.function.typedBody {returnType := closureType} context
      [observed.makeShape.initialized.id, observed.makeShape.outerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved context
      (.statements true [observed.makeShape.initialized.id, observed.makeShape.outerReturn.id]) closureType := by
  obtain ⟨middle, firstFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.makeShape.initializedFound first
  rw [observed.makeShape.initializedForm] at firstForm
  have remaining : GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved middle
      (.statements true [observed.makeShape.outerReturn.id]) closureType := by
    obtain ⟨_, _, _, returned, _⟩ := head_tail tail
    have actual := form_at unique observed.makeShape.outerReturnFound returned
    rw [observed.makeShape.outerReturnForm] at actual
    cases actual with
    | returnValue expression =>
      exact .body (.returnValue [] observed.makeShape.outerReturnFound observed.makeShape.outerReturnForm
        observed.makeShape.outerReturnType observed.makeShape.expressionFound observed.makeShape.expressionType
        (by simpa only [observed.makeShape.expressionType] using expression) formation)
  cases firstForm with
  | letInitialized value mono extended =>
    exact .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
      observed.make_local_declaration mono extended
      (by simp [observed.makeShape.inputs, Ne.symm observed.makeShape.localDistinct])
      observed.makeShape.initial.value.found
      (by rw [observed.makeShape.initial.value.type, observed.makeShape.localScheme]; rfl)
      (by simpa only [observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.initial.value.type] using value)
      initial remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [observed.makeShape.localScheme]; rfl))

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationMakeSupport
/-! Concrete make support and the complete closure family for the two-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.outerExpression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.outerExpression.id = .ok (observed.makeShape.outerExpression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.outerExpression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.outerExpression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.outerExpression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.outerExpression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic receiver included fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.outerExpression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.outerExpressionFound
  · exact observed.makeShape.outerLambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.outerRequirements
  · exact observed.makeShape.outerCoercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]
    exact .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
      (.returnValue [] observed.makeShape.outerReturnFound observed.makeShape.outerReturnForm)
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact observed.outer_body_syntax (actual.source ▸ actual.header.unique) True.intro True.intro typed

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.outerExpression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression receiver included
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_rows {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized = observed.identityRow.row ∨ named.specialized = observed.makeRow.row := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index := by
    have distinct := observed.identityMake
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact identityHeader.prepared.same
  · right
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact makeHeader.prepared.same

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody := by
  rcases observed.cached_rows identityHeader makeHeader selected with same | same
  · exact .inl (congrArg (fun row => row.function.typedBody) same)
  · exact .inr (congrArg (fun row => row.function.typedBody) same)

theorem ObservedProgram.cached_assumptions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized.assumptions = [] := by
  rcases observed.cached_rows identityHeader makeHeader selected with same | same
  · rw [same]; exact observed.identityRow.assumptions
  · rw [same]; exact observed.makeRow.assumptions

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    (parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id]) ∨
      (parameters = [] ∧ result = closureType ∧
        body = [observed.makeShape.initialized.id, observed.makeShape.outerReturn.id]) := by
  rcases observed.make_expressions found with same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.makeShape.initialRead.form] at form; cases form
  · rw [observed.makeShape.initial.calleeForm] at form; cases form
  · rw [observed.makeShape.initial.form] at form; cases form
  · rw [observed.makeShape.read.form] at form; cases form
  · rw [observed.makeShape.call.calleeForm] at form; cases form
  · rw [observed.makeShape.call.form] at form; cases form
  · rw [observed.makeShape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact .inl ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
  · rw [observed.makeShape.outerLambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact .inr ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.make_input_types_observed {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationLambdaSites
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedProgram.inner_owned {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner :=
  graph.nodesOwned _ (lookupExpression?_sound observed.makeShape.expressionFound).1

theorem ObservedProgram.inner_read {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id =
      .ok (observed.makeShape.expression, Core.CallableContract.functionType .unit .word) := by
  simp [SourceCoreCompatibleDataExpressions.readExpression, observed.inner_owned graph,
    observed.makeShape.expressionFound, observed.makeShape.requirements, observed.makeShape.coercions,
    SourceCoreCompatibleDataExpressions.projectType, SourceCoreCompatibleCatalog.Checked.project,
    observed.makeShape.expressionType, closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile,
    Core.CallableContract.functionType, Core.TaggedFunction.functionType, Core.TaggedFunction.identityType,
    Core.LanguageResult.resultType, Core.Ty.isWellFormed,
    TypeSystem.Ty.unit, TypeSystem.Ty.word]
  rfl

def ObservedProgram.inner_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (caller : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (same : caller.function.source = observed.makeRow.row.function.typedBody)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.ReturnLambda caller
      observed.makeShape.expression.id where
  node := observed.makeShape.expression
  reported := Core.CallableContract.functionType .unit .word
  parameters := []
  result := .word
  statement := observed.makeShape.innerReturn.id
  returnNode := observed.makeShape.innerReturn
  expression := observed.makeShape.call.value.node.id
  found := by rw [same]; exact observed.makeShape.expressionFound
  form := observed.makeShape.lambda
  owner := by rw [same]; exact observed.inner_owned graph
  requirements := observed.makeShape.requirements
  coercions := observed.makeShape.coercions
  ordinary := by rw [observed.noLocals]; rfl
  read := by rw [same]; exact observed.inner_read graph
  returnFound := by rw [same]; exact observed.makeShape.innerReturnFound
  returnForm := observed.makeShape.innerReturnForm
  returnType := observed.makeShape.innerReturnType

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader support.caller.selected with original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
    have found := code.sourceFound
    rw [sameSource] at found
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader support.caller.selected))
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    have signatureMember : fixture.makeSignature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
      rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)
    have sourceOwner : function.source.owner = fixture.makeSignature.id := by
      rw [sameSource]; exact observed.makeRow.sourceOwner
    rcases observed.make_lambda_shape found code.sourceForm with inner | outer
    · have bodyShape := inner.2.2
      have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
          function.source observed.makeShape.call.value.node.id function.body := by
        rw [bodyShape]
        exact .returning [] (by rw [sameSource]; exact observed.makeShape.innerReturnFound)
          observed.makeShape.innerReturnForm
      have tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
          function.source observed.makeShape.call.value.node.id := by
        rw [sameSource]; exact observed.make_syntax
      obtain ⟨packet, canonical⟩ :=
        CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport.of_actual
          stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
          signatureMember sourceOwner observed.makeShape.call.value.node.id terminal tree _ (.anonymous selected)
      exact ⟨⟨.canonicalTerminal packet, canonical⟩⟩
    · have resultType := outer.2.1
      have bodyShape := outer.2.2
      have original : support.caller.function.source = function.source :=
        support.caller.agreement.source.trans support.source.symm
      have graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody := by
        rw [← sameSource]; exact support.body.frame.code.graph
      have typed := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
        support.body.frame support.body.extended
      obtain ⟨finalContext, facts, typed, _completes⟩ := typed
      have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
        rw [sameSource, bodyShape]; exact observed.outer_body_shape
      have tree : GenericImperativeMatch.Syntax function.source
          (CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport.Syntax support.caller)
          support.body.context (.statements true function.body) function.resultType := by
        rw [sameSource, bodyShape, resultType] at typed ⊢
        apply observed.outer_body_syntax (sameSource ▸ support.body.unique)
        · exact .general (by rw [original, sameSource]; exact observed.make_initial_syntax)
        · exact .formation (observed.inner_shape support.caller (original.trans sameSource) graph)
        · exact typed
      obtain ⟨packet, nested⟩ :=
        CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport.of_actual
          stagePrepared code support provenance prefixContext receiver fixture.source_wellFormed metadata
          rows complete signatureMember sourceOwner
          (bootstrap_zero fixture.recipe.compiled)
          observed.profile shape tree.prepared _ (.anonymous selected)
      exact ⟨⟨.nestedBranching packet, nested⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, makeHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have headerKey := (selected_key selected).trans key
  rcases List.mem_cons.mp selected.member with same | rest
  · rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.identityRow.keys_ne observed.makeRow observed.identityMake headerKey)
  · exact List.mem_singleton.mp rest

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

theorem selected_make_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, makeHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root identityHeader makeHeader request.selected (started_key request)

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.identity_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.identityShape.returns]
  rfl

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.make_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = outerType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  makeRow : makeInput.row = observed.makeRow.row
  identityPacket : Issued identityInput
  makePacket : Issued makeInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  makeHeader : ActualHeader fixture observed.makeRow.row
  identityEq : identityHeader.header = identityPacket.header
  makeEq : makeHeader.header = makePacket.header
  rows : Inventory [identityInput, makeInput]
  rowsEq : rows = .cons identityPacket (.cons makePacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, makeInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers rows → Terminal header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.identityHeader.header, support.makeHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.identityEq, support.makeEq]

private def selectTwo {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (distinct : first.slot ≠ second.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second) :
    ∀ header, header ∈ [first, second] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (distinct (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ secondValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, makeInput, identityRow, makeRow,
    identityPacket, makePacket, identityHeader, makeHeader,
    identityEq, makeEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, makeInput] :=
    .cons identityPacket (.cons makePacket .nil)
  have headerList : headers rows = [identityHeader.header, makeHeader.header] := by
    simp only [rows, headers, identityEq, makeEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have identityInputIndex : identityHeader.header.slot = identityInput.prepared.index := by
    rw [identityEq]; exact identityPacket.aligned.slot
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have identityMake : identityHeader.header.slot ≠ makeHeader.header.slot := by
    rw [identityIndex, makeIndex]
    exact observed.identityMake
  have identityMakeInput : identityInput.prepared.index ≠ makeInput.prepared.index := by
    rw [← identityInputIndex, ← makeInputIndex]
    exact identityMake
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.outerExpression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint receiver (fun _ _ represented => represented) (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨identityTerminal, _identityExpression, identitySupport⟩ :=
    identityHeader.identity_support observed receiver (actualStagePrepared fixture)
  obtain ⟨identitySupport⟩ := identitySupport
  let property := fun header => Σ terminal : Terminal header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo identityMake property
      ⟨identityTerminal, .recursive identitySupport⟩ ⟨makeTerminal, makeSupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    makeInput := makeInput
    identityRow := identityRow
    makeRow := makeRow
    identityPacket := identityPacket
    makePacket := makePacket
    identityHeader := identityHeader
    makeHeader := makeHeader
    identityEq := identityEq
    makeEq := makeEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [identityMakeInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family identityHeader makeHeader rows complete (actualStagePrepared fixture) receiver association
    identityDescriptor := identityHeader.descriptor identityStages
    makeDescriptor := makeHeader.descriptor makeStages }⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.makeRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.bodies {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.makeHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.bodies
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩




theorem selected_function {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {raw : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value} {handle : SourceCorePublicValues.Handle}
    (same : publicValue = .function handle) {source : Dynamic.Value} {native : Core.Value}
    {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicNestedOutputSelections.Selected checked session
      (same.symm ▸ RecursiveNamedPublicNestedOutputSelections.Selection.function (type := raw))
      source native nativeType fuel entries) :
    entries = [⟨raw, source, handle, native, nativeType, fuel⟩] := by
  cases same
  cases selected
  rfl

/-- The function returned by an actual outer closure joins the current history. -/
theorem invoke_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = outerType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = outerType)
    (call : ObservedFormation publicSession handle)
    (invocation : Staging.Recursive.Scope) :
    ∃ (inner : Entry), inner.sourceType = closureType ∧ inner.handle = call.handle ∧
      call.handle.sourceType = closureType ∧
      ∃ (sources : List Dynamic.Value)
        (after : RetainedState support call.completion.session (entries ++ [inner])),
      Dynamic.ValuesPack sources .unit ∧
      SourceInvocation support invocation state.heap entry.source sources (.value inner.source) after.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, started, _parameterView, _resultView,
    succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family support.bodies support.supports
      fixture.source_wellFormed state.history entry member entryType input state.atRecipe
      state.registry state.atSession (by simpa only [entryHandle] using call.executed)
      (call.returned.symm ▸ RecursiveNamedPublicNestedOutputSelections.Selection.function) invocation
  let inner : Entry := ⟨closureType, source, call.handle, payload, nativeResult, runOptions.outputValidationFuel⟩
  have addedEq : added = [inner] := selected_function call.returned selected
  have exactHandle : entry.handle.sourceType = outerType := entryHandle ▸ handleType
  have requested := started.requested_exact exactHandle
  have innerType := succeeded.function_source_type requested (actualAt.1.symm.trans call.returned)
  let next : RetainedState support call.completion.session (entries ++ [inner]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := addedEq ▸ retained }
  exact ⟨inner, rfl, rfl, innerType, sources, next, packing, sourceSize, trace⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = outerType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = outerType ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_make_at support.identityHeader support.makeHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.makeHeader.make_input_types]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.makeDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := by
      have registered := request.started.returned_registry succeeded
      rw [registryAt] at registered
      exact registered
    history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = outerType
    rw [selected]
    exact support.makeHeader.make_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.make
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = outerType ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.make_typed_handle call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured local cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = outerType ∧ entry.handle = first.handle ∧
      first.handle.sourceType = outerType ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.makeHeader.header support.makeInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.makePacket.header.named.specialized support.makeInput.prepared.available)) := by
    rw [support.makeEq]
    exact support.makePacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
      first.started first.executed first.returned support.makeDescriptor
  let entry : Entry := ⟨support.makeHeader.header.function.resultType, source, first.handle,
    payload, support.makeHeader.header.output, runOptions.outputValidationFuel⟩
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.completion.session [entry] := {
    artifact := artifact
    session := returnedCompletion.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.makeHeader.make_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.makeInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = outerType ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationPublicExecution
/-! Seven actual public calls retain both generations of captured closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  firstInner : Entry
  second : Entry
  secondInner : Entry
  firstType : first.sourceType = outerType
  firstHandle : first.handle = sequence.first.handle
  firstHandleType : sequence.first.handle.sourceType = outerType
  firstInnerType : firstInner.sourceType = closureType
  firstInnerHandle : firstInner.handle = sequence.firstFormation.handle
  firstInnerHandleType : sequence.firstFormation.handle.sourceType = closureType
  secondType : second.sourceType = outerType
  secondHandle : second.handle = sequence.second.handle
  secondHandleType : sequence.second.handle.sourceType = outerType
  secondInnerType : secondInner.sourceType = closureType
  secondInnerHandle : secondInner.handle = sequence.secondFormation.handle
  secondInnerHandleType : sequence.secondFormation.handle.sourceType = closureType
  distinctOuter : first.handle ≠ second.handle
  distinctInner : firstInner.handle ≠ secondInner.handle
  initial : RetainedState support sequence.first.completion.session [first]
  firstFormationState : RetainedState support sequence.firstFormation.completion.session [first, firstInner]
  secondState : RetainedState support sequence.second.completion.session [first, firstInner, second]
  secondFormationState : RetainedState support sequence.secondFormation.completion.session [first, firstInner, second, secondInner]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, firstInner, second, secondInner]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, firstInner, second, secondInner]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, firstInner, second, secondInner]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstFormationState.heap [.word secondSeed] (.value second.source) secondState.heap
  firstFormationArguments : List Dynamic.Value
  firstFormationPacking : Dynamic.ValuesPack firstFormationArguments .unit
  firstFormationTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap first.source firstFormationArguments (.value firstInner.source) firstFormationState.heap
  secondFormationArguments : List Dynamic.Value
  secondFormationPacking : Dynamic.ValuesPack secondFormationArguments .unit
  secondFormationTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap second.source secondFormationArguments (.value secondInner.source) secondFormationState.heap
  firstReadArguments : List Dynamic.Value
  firstReadPacking : Dynamic.ValuesPack firstReadArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondFormationState.heap firstInner.source firstReadArguments (.value (.word seed)) firstReadState.heap
  secondReadArguments : List Dynamic.Value
  secondReadPacking : Dynamic.ValuesPack secondReadArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap secondInner.source secondReadArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedReadArguments : List Dynamic.Value
  repeatedReadPacking : Dynamic.ValuesPack repeatedReadArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap firstInner.source repeatedReadArguments (.value (.word seed)) finalState.heap

/-- Exact exported raw types separate outer from inner handles; genuine
issuance observations distinguish the two captures within each generation. -/
theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    [meaning.first.handle, meaning.firstInner.handle, meaning.second.handle, meaning.secondInner.handle].Nodup := by
  have different : ∀ (outer inner : SourceCorePublicValues.Handle),
      outer.sourceType = outerType → inner.sourceType = closureType → outer ≠ inner := by
    intro outer inner outerRaw innerRaw same
    have types := congrArg SourceCorePublicValues.Handle.sourceType same
    rw [outerRaw, innerRaw] at types
    cases types
  have firstRaw : meaning.first.handle.sourceType = outerType := by
    rw [meaning.firstHandle]; exact meaning.firstHandleType
  have secondRaw : meaning.second.handle.sourceType = outerType := by
    rw [meaning.secondHandle]; exact meaning.secondHandleType
  have firstInnerRaw : meaning.firstInner.handle.sourceType = closureType := by
    rw [meaning.firstInnerHandle]; exact meaning.firstInnerHandleType
  have secondInnerRaw : meaning.secondInner.handle.sourceType = closureType := by
    rw [meaning.secondInnerHandle]; exact meaning.secondInnerHandleType
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨different _ _ firstRaw firstInnerRaw, meaning.distinctOuter,
      different _ _ firstRaw secondInnerRaw⟩,
    ⟨Ne.symm (different _ _ secondRaw firstInnerRaw), meaning.distinctInner⟩,
    different _ _ secondRaw secondInnerRaw⟩

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨firstInner, firstInnerType, firstInnerHandle, firstInnerHandleType,
      firstFormationArguments, firstFormationState, firstFormationPacking, firstFormationTrace⟩ :=
    invoke_formation initial first (by simp) firstType firstHandle firstHandleType sequence.firstFormation scope
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    firstFormationState.make_typed_handle sequence.second scope
  obtain ⟨secondInner, secondInnerType, secondInnerHandle, secondInnerHandleType,
      secondFormationArguments, secondFormationState, secondFormationPacking, secondFormationTrace⟩ :=
    invoke_formation secondState second (by simp) secondType secondHandle secondHandleType sequence.secondFormation scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstReadArguments, firstReadState, firstReadPacking, firstReadTrace⟩ :=
    invoke_word secondFormationState firstInner (by simp) firstInnerType firstInnerHandle firstInnerHandleType
      (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨secondReadArguments, secondReadState, secondReadPacking, secondReadTrace⟩ :=
    invoke_word firstReadState secondInner (by simp) secondInnerType secondInnerHandle secondInnerHandleType
      (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedReadArguments, finalState, repeatedReadPacking, repeatedReadTrace⟩ :=
    invoke_word secondReadState firstInner (by simp) firstInnerType firstInnerHandle firstInnerHandleType
      (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, firstInner, second, secondInner,
    firstType, firstHandle, firstHandleType, firstInnerType, firstInnerHandle, firstInnerHandleType,
    secondType, secondHandle, secondHandleType, secondInnerType, secondInnerHandle, secondInnerHandleType,
    distinctOuter := by rw [firstHandle, secondHandle]; exact sequence.distinctOuter
    distinctInner := by rw [firstInnerHandle, secondInnerHandle]; exact sequence.distinctInner
    initial, firstFormationState, secondState, secondFormationState, firstReadState, secondReadState, finalState,
    firstTrace, secondTrace, firstFormationArguments, firstFormationPacking, firstFormationTrace,
    secondFormationArguments, secondFormationPacking, secondFormationTrace,
    firstReadArguments, firstReadPacking, firstReadTrace, secondReadArguments, secondReadPacking, secondReadTrace,
    repeatedReadArguments, repeatedReadPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages sequence receiver⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationFormationForward
/-! Independent Source success at an outer closure produces a reusable inner
function and preserves the exact reached heap for every sufficient public resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardFormationAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
          ∃ inner : Entry, inner.sourceType = closureType ∧ inner.source = source ∧
            completion.value = .function inner.handle ∧ inner.handle.sourceType = closureType ∧
            ∃ returned : RetainedState support completion.session (entries ++ [inner]), returned.heap = after

theorem forward_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = outerType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = outerType)
    (call : ObservedFormation publicSession handle) (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {source : Dynamic.Value} (packing : Dynamic.ValuesPack arguments .unit)
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value source) after) :
    ForwardFormationAt support publicSession entries handle source after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have requested := started.requested_exact handleType
  have checkpointReady := original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp exportsReady)
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollectionPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family support.bodies support.supports
      fixture.source_wellFormed state.history entry member entryType unitInput state.atRecipe state.registry
      (state.atSession.exportsReady_iff.mp exportsReady) started packing trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, succeeded, exported, actualAt,
      registry, ready, collect⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded atCheckpoint resumed checkpointReady
      (nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  obtain ⟨reached, added, selected, _handles, _related, retained⟩ :=
    collect (functionValue.symm ▸ RecursiveNamedPublicNestedOutputSelections.Selection.function)
  let inner : Entry := ⟨closureType, source, handle, payload, nativeResult, outputFuel⟩
  have addedEq : added = [inner] := selected_function functionValue selected
  let returned : RetainedState support completion.session (entries ++ [inner]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := addedEq ▸ retained }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr ready,
    inner, rfl, rfl, functionValue, handleType, returned, rfl⟩

def FormationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  ForwardFormationAt meaning.support sequence.first.completion.session [meaning.first]
    sequence.first.handle meaning.firstInner.source meaning.firstFormationState.heap ∧
  ForwardFormationAt meaning.support sequence.second.completion.session [meaning.first, meaning.firstInner, meaning.second]
    sequence.second.handle meaning.secondInner.source meaning.secondFormationState.heap

theorem SequenceWitness.formations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : FormationForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have firstFormationReady := sequence.firstFormation.executed.exportsReady firstReady
  have secondReady := sequence.second.executed.exportsReady firstFormationReady
  exact ⟨forward_formation meaning.initial meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.firstFormation firstReady
      meaning.firstFormationPacking meaning.firstFormationTrace,
    forward_formation meaning.secondState meaning.second (by simp)
      meaning.secondType meaning.secondHandle meaning.secondHandleType sequence.secondFormation secondReady
      meaning.secondFormationPacking meaning.secondFormationTrace⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel outerType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world outerType source payload nativeType

/-- A factory result enters the returned history with its exact Source value. -/
def ReturnedOuter {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value)
    (after : Dynamic.Heap) (fuel : Nat) : Prop :=
  ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
    entry.sourceType = outerType ∧ entry.source = source ∧
    completion.value = .function entry.handle ∧ entry.handle.sourceType = outerType ∧
    ∃ returned : RetainedState support completion.session (entries ++ [entry]),
      returned.heap = after ∧ ReturnedValue completion returned source fuel

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedOuter support completion [] source after outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.bodies)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  have requestedRaw := requested
  rw [support.makeHeader.make_result_type] at requested
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  have checkpointReady := started.original.initial_registry.exportsReady (sessionAt.exportsReady_iff.mp initialReady)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, _reached, succeeded, exported, actualAt,
      _related, _history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨support.makeHeader.header.function.resultType, source, handle, _payload, support.makeHeader.header.output, outputFuel⟩
  obtain ⟨returnedCaller, related, post⟩ := _fullResult.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl started selected exported _fullResult
    returnedCaller ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  let returned : RetainedState support completion.session [entry] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld outerType source _payload support.makeHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.makeHeader.make_result_type] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr ready,
    entry, support.makeHeader.make_result_type, rfl, functionValue, handleType,
    returned, rfl, _payload, _, encoded, represented⟩



end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationInvocationForward
/-! The three captured closure calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit .word)
    {word : Core.Word}
    (call : ObservedInvocation publicSession handle .unit)
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    (packing : Dynamic.ValuesPack arguments .unit)
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle word after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  subst nativeResult
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (support.bodies)
      support.supports fixture.source_wellFormed state.history entry member entryType
      unitInput state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started packing trace atCheckpoint
  have payloadEq : payload = .word word := by
    have represented := fullResult.1
    cases represented with
    | value related =>
      obtain ⟨actual, sourceEq, nativeEq⟩ := CompatibleExpressionPrimitives.word_fields related
      cases Dynamic.Value.word.inj sourceEq
      exact nativeEq
  subst payload
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, atCompletion,
      _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  have valueEq : completion.value = .word word := atCompletion.1.trans (exported.word_value requested)
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨completion, succeeded, valueEq, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

/-- Each inner closure keeps its own captured value at every sufficient budget. -/
def InvocationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  ForwardWordAt meaning.support sequence.secondFormation.completion.session
    [meaning.first, meaning.firstInner, meaning.second, meaning.secondInner]
    sequence.firstFormation.handle seed meaning.firstReadState.heap ∧
  ForwardWordAt meaning.support sequence.firstRead.completion.session
    [meaning.first, meaning.firstInner, meaning.second, meaning.secondInner]
    sequence.secondFormation.handle secondSeed meaning.secondReadState.heap ∧
  ForwardWordAt meaning.support sequence.secondRead.completion.session
    [meaning.first, meaning.firstInner, meaning.second, meaning.secondInner]
    sequence.firstFormation.handle seed meaning.finalState.heap

theorem SequenceWitness.invocations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : InvocationForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have firstFormationReady := sequence.firstFormation.executed.exportsReady firstReady
  have secondReady := sequence.second.executed.exportsReady firstFormationReady
  have secondFormationReady := sequence.secondFormation.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondFormationReady
  have secondReadReady := sequence.secondRead.executed.exportsReady firstReadReady
  exact ⟨forward_word meaning.secondFormationState meaning.firstInner (by simp)
      meaning.firstInnerType meaning.firstInnerHandle meaning.firstInnerHandleType sequence.firstRead secondFormationReady
      meaning.firstReadPacking meaning.firstReadTrace,
    forward_word meaning.firstReadState meaning.secondInner (by simp)
      meaning.secondInnerType meaning.secondInnerHandle meaning.secondInnerHandleType sequence.secondRead firstReadReady
      meaning.secondReadPacking meaning.secondReadTrace,
    forward_word meaning.secondReadState meaning.firstInner (by simp)
      meaning.firstInnerType meaning.firstInnerHandle meaning.firstInnerHandleType sequence.repeatedRead secondReadReady
      meaning.repeatedReadPacking meaning.repeatedReadTrace⟩

end Tests.SourceCoreNestedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreNestedFormationForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value])
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedOuter support completion entries source after outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.identityHeader support.makeHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.bodies) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have requestedRaw := requested
  rw [selectedHeader, support.makeHeader.make_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, _reached, succeeded, exported, actualAt,
      _related, _history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨returnedCaller, related, post⟩ := fullResult.2.2.2.2.2.2.2
  have prior := RecursiveNamedPublicHistoryRegistryExtension.extend_history state.history extended
  have retained := RecursiveNamedPublicFunctionHistory.History.next prior rfl request.started request.selected
    exported fullResult returnedCaller ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  let returned : RetainedState support completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld outerType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = outerType := by rw [selectedHeader]; exact support.makeHeader.make_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  have entryType : entry.sourceType = outerType := by
    change request.header.function.resultType = outerType
    rw [selectedHeader]
    exact support.makeHeader.make_result_type
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, entryType, rfl, functionValue, handleType, returned, rfl, payload, _, encoded, represented⟩


/-- Both factories, both nested formations, and all three retained inner calls
have sufficient execution and export budgets at their original checkpoints. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first, meaning.firstInner]) meaning.support sequence.second
    meaning.second.source meaning.secondState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have formationReady := sequence.firstFormation.executed.exportsReady firstReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_make meaning.firstFormationState sequence.second formationReady meaning.secondTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver,
        [meaning.first.handle, meaning.firstInner.handle, meaning.second.handle, meaning.secondInner.handle].Nodup ∧
        ForwardMeaning meaning ∧ FormationForwardMeaning meaning ∧ InvocationForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra identityStages makeStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.handles_distinct, meaning.forward, meaning.formations_forward, meaning.invocations_forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let identityStages ← observeStages fixture observed.identityRow
  let makeStages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra identityStages makeStages sequence
  IO.println "Nested formation: make10/A/a, make20/B/b, a10/b20/a10; four retained handles, exact Source heaps/history, all seven public fuel bounds proved"

end Tests.SourceCoreNestedFormation
end
