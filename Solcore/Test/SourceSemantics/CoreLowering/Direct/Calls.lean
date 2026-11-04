import Solcore.Test.SourceSemantics.CoreLowering.OperatorCalls
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
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
import Solcore.Test.SourceSemantics.CoreLowering.Captured.Locals
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectWordForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation

/-!
# Direct call tests

Direct calls, issued calls and outputs through public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics
structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .unit .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerReturnForm : innerReturn.form = .returnStmt (some read.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = .function .unit .word
  expressionType : expression.type = .function .unit .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .word

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

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .word
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      · rw [shape.readRequirements, shape.readCoercions, shape.readType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function relay(seed: Word) returns (function() returns (Word)) { return make(identity(seed)); }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured factory roots"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured factory readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "captured factory readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "captured factory readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured factory readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured factory readCoercions"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some read.id)) "captured factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .unit .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .unit .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "captured factory statementType"
  return { binder, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }


abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev IdentityShape := Tests.SourceCoreOperatorCalls.IdentityShape
abbrev closureType : TypeSystem.Ty := .function .unit .word

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]

/-- Exact original metadata of a monomorphic direct call. -/
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (expected : TypeSystem.Ty) where
  callee : TypedNode source (.function .word expected)
  value : TypedNode source expected
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[], [], .function .word expected⟩
  inputs : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [expected]
  exact : instantiation = ⟨signature.id, [], .function .word expected, [],
    signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {expected : TypeSystem.Ty}
    (call : DirectCall source signature argument expected) {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions)
    (admissible : TypeAdmissible context expected)
    (argumentTyped : ExpressionHasType source context argument .word) :
    ExpressionHasType source context call.value.node.id expected := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · simpa only [call.scheme] using ParameterSubstitution.exact_empty
    · intro parameter replacement contained; cases contained
    · simp [call.scheme, parameter_nil]
    · simp [call.scheme]
  have application : DeclarationApplicationValid context call.instantiation [.word] expected [] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, parameter_nil]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons argumentTyped (.nil _)))
      call.value.raw admissible (call.value.type.symm ▸ admissible) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) .nil rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RelayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  inner : DirectCall function.typedBody identity read.node.id .word
  outer : DirectCall function.typedBody maker inner.value.node.id closureType
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some outer.value.node.id)
  statementType : statement.type = closureType

def RelayShape.nodeList {function signature identity maker} (shape : RelayShape function signature identity maker) : List Node :=
  [.expression shape.read.node, .expression shape.inner.callee.node, .expression shape.inner.value.node,
   .expression shape.outer.callee.node, .expression shape.outer.value.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity maker}
    (shape : RelayShape function signature identity maker) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (makeMember : maker ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := closureType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have inner := shape.inner.typed (fields ▸ identityMember) word read
    have outer := shape.outer.typed (fields ▸ makeMember) callable inner
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm outer shape.statementType)⟩

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (callee value : ExpressionNode) (expected : TypeSystem.Ty) :
    IO (DirectCall source signature argument expected) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function .word expected)
  let value ← Tests.SourceCoreOperatorCalls.observeNode source value expected
  let .reference name (.declaration instantiation) := callee.node.form
    | throw (IO.userError "direct synthetic declaration callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "direct callee"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.declaration instantiation)) "direct call"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[], [], .function .word expected⟩) "direct signature"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.word]) "direct parameter"
  let ⟨returns⟩ ← observed (signature.returnTypes = [expected]) "direct return"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [], .function .word expected, [],
    signature.parameterComptime, signature.returnComptime⟩) "direct exact metadata"
  return {callee, value, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}

def relayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) :
    IO (RelayShape function signature identity maker) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay input")
  let [.expression read, .expression innerCallee, .expression innerValue,
      .expression outerCallee, .expression outerValue, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "relay original nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .word
  let inner ← observeDirect function.typedBody identity read.node.id innerCallee innerValue .word
  let outer ← observeDirect function.typedBody maker inner.value.node.id outerCallee outerValue closureType
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "relay parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "relay inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType]) "relay returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "relay inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "relay binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "relay binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "relay roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some outer.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = closureType) "relay statementType"
  return {binder, read, inner, outer, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, roots, statementFound, statementForm, statementType}

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  makeFunction : CheckedFunction
  relayFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  makeSignature : ProgramFunctionSignature
  relaySignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, makeFunction, relayFunction]
  signatures : program.signatures.functions = [identitySignature, makeSignature, relaySignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  makeRelay : makeSignature.id ≠ relaySignature.id
  identityShape : IdentityShape identityFunction identitySignature
  makeShape : FactoryShape makeFunction makeSignature
  relayShape : RelayShape relayFunction relaySignature identitySignature makeSignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, makeFunction, relayFunction], [identitySignature, makeSignature, relaySignature] =>
      let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
      let makeShape ← shape makeFunction makeSignature
      let relayShape ← relayShape relayFunction relaySignature identitySignature makeSignature
      let ⟨methods⟩ ← observed (program.methods = []) "direct fixture methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "direct fixture identityDeclaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "direct fixture makeDeclaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "direct fixture relayDeclaration"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "direct fixture identityMake"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "direct fixture identityRelay"
      let ⟨makeRelay⟩ ← observed (makeSignature.id ≠ relaySignature.id) "direct fixture makeRelay"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "direct fixture identityNodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "direct fixture makeNodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "direct fixture relayNodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures
          · exact False.elim (makeRelay (makeDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact False.elim (makeRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program := program
        checked := checked
        wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction := identityFunction
        makeFunction := makeFunction
        relayFunction := relayFunction
        identitySignature := identitySignature
        makeSignature := makeSignature
        relaySignature := relaySignature
        functions := functions
        signatures := signatures
        methods := methods
        identityDeclaration := identityDeclaration
        makeDeclaration := makeDeclaration
        relayDeclaration := relayDeclaration
        identityMake := identityMake
        identityRelay := identityRelay
        makeRelay := makeRelay
        identityShape := identityShape
        makeShape := makeShape
        relayShape := relayShape
        identityNodes := identityNodes
        makeNodes := makeNodes
        relayNodes := relayNodes
      }
    | _, _ => throw (IO.userError "direct fixture declaration count")

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
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
    SourceCompiler.Seed.declaration checked.makeSignature.id, SourceCompiler.Seed.declaration checked.relaySignature.id]
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
  relayRow : ObservedRow fixture fixture.relaySignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 3
  identityMake : identityRow.index ≠ makeRow.index
  identityRelay : identityRow.index ≠ relayRow.index
  makeRelay : makeRow.index ≠ relayRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature
  relayShape : RelayShape relayRow.row.function fixture.relaySignature fixture.identitySignature fixture.makeSignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  makeNodes : makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  relayNodes : relayRow.row.function.typedBody.nodes = relayShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let makeRow ← observeRow fixture fixture.makeSignature
  let relayRow ← observeRow fixture fixture.relaySignature
  let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityRow.row.function fixture.identitySignature
  let makeShape ← shape makeRow.row.function fixture.makeSignature
  let relayShape ← relayShape relayRow.row.function fixture.relaySignature fixture.identitySignature fixture.makeSignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 3) "direct compiled globalsLength"
  let ⟨identityMake⟩ ← observed (identityRow.index ≠ makeRow.index) "direct compiled identityMake"
  let ⟨identityRelay⟩ ← observed (identityRow.index ≠ relayRow.index) "direct compiled identityRelay"
  let ⟨makeRelay⟩ ← observed (makeRow.index ≠ relayRow.index) "direct compiled makeRelay"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "direct compiled identityNodes"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "direct compiled makeNodes"
  let ⟨relayNodes⟩ ← observed (relayRow.row.function.typedBody.nodes = relayShape.nodeList) "direct compiled relayNodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "direct compiled noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "direct compiled profile"
  return {identityRow, makeRow, relayRow, identityShape, makeShape, relayShape, globalsLength, identityMake, identityRelay, makeRelay, identityNodes, makeNodes, relayNodes, noLocals, profile}

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

/-- All three real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (identityInput makeInput relayInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ makeInput.row = observed.makeRow.row ∧ relayInput.row = observed.relayRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (relayPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (makeHeader : ActualHeader fixture observed.makeRow.row)
        (relayHeader : ActualHeader fixture observed.relayRow.row),
        identityHeader.header = identityPacket.header ∧ makeHeader.header = makePacket.header ∧ relayHeader.header = relayPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons identityPacket (.cons makePacket (.cons relayPacket .nil)))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨relayInput, relayRow, relayPacket, relayHeader, relayEq, relaySlot, relaySignature⟩ := observed.relayRow.issue
  refine ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .tail _ (.head _)
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨relayHeader.header, ?_, relaySlot.trans same.symm, ?_⟩
    · rw [relayEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.relayRow.slot.selected] at found
      exact relaySignature.trans (Option.some.inj found)

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
  rw [observed.identityNodes, Tests.SourceCoreOperatorCalls.IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.identityShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.relay_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.relayRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.relayNodes, RelayShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  all_goals try cases same
  · rw [observed.relayShape.read.form] at form; cases form
  · rw [observed.relayShape.inner.calleeForm] at form; cases form
  · rw [observed.relayShape.inner.form] at form; cases form
  · rw [observed.relayShape.outer.calleeForm] at form; cases form
  · rw [observed.relayShape.outer.form] at form; cases form

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

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsIdentitySupport
/-! The actual identity row is a compiler-produced read body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem identity_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.identityRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.identityShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.identityNodes] at present
  simpa only [Tests.SourceCoreOperatorCalls.IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
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

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsMakeSupport
/-! Concrete make support and the complete closure family for the three-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact observed.makeShape.innerReturnFound
  · exact observed.makeShape.innerReturnForm
  · exact observed.makeShape.innerReturnType

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
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayHeader.prepared.same

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.makeShape.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.makeShape.lambda] at form
        obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
        exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
      · rcases List.mem_cons.mp rest with impossible | empty
        · cases impossible
        · cases empty

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader relayHeader support.caller.selected with original | original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.relay_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
      (by rw [sameSource]; exact observed.makeRow.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)


theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsReadSupport
/-! Finite original Source facts for nested direct declaration calls. The
synthetic callee references carry static catalog metadata; only the original
ordered argument expressions are evaluated recursively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.read.node ∨ node = observed.relayShape.inner.callee.node ∨
    node = observed.relayShape.inner.value.node ∨ node = observed.relayShape.outer.callee.node ∨
    node = observed.relayShape.outer.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    (named : CallableIndexedNamedGeneration.Named)
    (same : named.specialized = observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same
    all_goals subst node
    · exact observed.relayShape.read.requirements
    · exact observed.relayShape.inner.callee.requirements
    · exact observed.relayShape.inner.value.requirements
    · exact observed.relayShape.outer.callee.requirements
    · exact observed.relayShape.outer.value.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same
    all_goals subst node
    · exact observed.relayShape.read.coercions
    · exact observed.relayShape.inner.callee.coercions
    · exact observed.relayShape.inner.value.coercions
    · exact observed.relayShape.outer.callee.coercions
    · exact observed.relayShape.outer.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same
    all_goals subst node
    · rw [observed.relayShape.read.form] at form
      cases form
    · rw [observed.relayShape.inner.calleeForm] at form
      cases form
    · rw [observed.relayShape.inner.form] at form
      cases form
    · rw [observed.relayShape.outer.calleeForm] at form
      cases form
    · rw [observed.relayShape.outer.form] at form
      cases form
  · intro _ _ _ _ _ _ _ _
    rw [same]
    exact observed.relayRow.assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.relay_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row) :
    GeneralSyntax actual.header.function.source observed.relayShape.outer.value.node.id := by
  rw [actual.source]
  refine .direct observed.relayShape.outer.value.found observed.relayShape.outer.form ?_ ?_
  · rw [observed.relayShape.outer.exact]
    exact ⟨rfl, rfl⟩
  · intro child member
    cases List.mem_singleton.mp member
    refine .direct observed.relayShape.inner.value.found observed.relayShape.inner.form ?_ ?_
    · rw [observed.relayShape.inner.exact]
      exact ⟨rfl, rfl⟩
    · intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.read observed.relayShape.read.found observed.relayShape.read.form)

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.relay_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.relayShape.outer.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.relayShape.outer.value.node.id
    observed.relayShape.statement observed.relayShape.roots observed.relayShape.statementFound observed.relayShape.statementForm
  have same : terminal.prepared.named.specialized = observed.relayRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (actual.relay_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.relay_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

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


structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.relayRow
  second : ObservedFunctionCall first.completion.session observed.relayRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  firstRead : ObservedInvocation second.completion.session first.handle .unit
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.relayRow.row.key [.word interveningSeed]
  secondRead : ObservedInvocation intervening.completion.session second.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.relayRow
  let second ← observeFunctionCall first.completion.session observed.relayRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let firstRead ← observeInvocation second.completion.session first.handle .unit
    if firstValue : firstRead.completion.value = .word seed then
      let intervening ← observeFunctionCall firstRead.completion.session observed.relayRow.row.key [.word interveningSeed]
      let secondRead ← observeInvocation intervening.completion.session second.handle .unit
      if secondValue : secondRead.completion.value = .word secondSeed then
        let repeatedRead ← observeInvocation secondRead.completion.session first.handle .unit
        if repeatedValue : repeatedRead.completion.value = .word seed then
          return {first, second, distinct, firstRead, firstValue, intervening, secondRead, secondValue, repeatedRead, repeatedValue}
        else throw (IO.userError "direct relay first capture changed after later calls")
      else throw (IO.userError "direct relay second capture not20")
    else throw (IO.userError "direct relay first capture not10")
  else throw (IO.userError "direct relay lost distinct captures")

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
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

theorem selected_relay_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, makeHeader.header, relayHeader.header] root header)
    (key : root.key = observed.relayRow.row.key) : header = relayHeader.header := by
  have headerKey := (selected_key selected).trans key
  rcases List.mem_cons.mp selected.member with same | rest
  · rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.identityRow.keys_ne observed.relayRow observed.identityRelay headerKey)
  · rcases List.mem_cons.mp rest with same | rest
    · rw [same, makeHeader.key] at headerKey
      exact False.elim (observed.makeRow.keys_ne observed.relayRow observed.makeRelay headerKey)
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

theorem selected_relay_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, makeHeader.header, relayHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.relayRow.row.key arguments fuel world store) : request.header = relayHeader.header := by
  subst headers
  exact selected_relay_root identityHeader makeHeader relayHeader request.selected (started_key request)

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

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
  have raw := actual.make_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.relay_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.relayShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.relay_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.relay_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.relay_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.relayShape.returns]
  rfl

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
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
  relayInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  makeRow : makeInput.row = observed.makeRow.row
  relayRow : relayInput.row = observed.relayRow.row
  identityPacket : Issued identityInput
  makePacket : Issued makeInput
  relayPacket : Issued relayInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  makeHeader : ActualHeader fixture observed.makeRow.row
  relayHeader : ActualHeader fixture observed.relayRow.row
  identityEq : identityHeader.header = identityPacket.header
  makeEq : makeHeader.header = makePacket.header
  relayEq : relayHeader.header = relayPacket.header
  rows : Inventory [identityInput, makeInput, relayInput]
  rowsEq : rows = .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, makeInput, relayInput].map (fun input => input.prepared.index)).Nodup
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
  relayDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.identityHeader.header, support.makeHeader.header, support.relayHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.identityEq, support.makeEq, support.relayEq]

private def selectThree {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second third : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (firstSecond : first.slot ≠ second.slot) (firstThird : first.slot ≠ third.slot)
    (secondThird : second.slot ≠ third.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second) (thirdValue : property third) :
    ∀ header, header ∈ [first, second, third] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (firstSecond (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstThird (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else if secondSlot : header.slot = second.slot then
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (secondThird (secondSlot.symm.trans other))
    exact same.symm ▸ secondValue
  else
    have same : header = third := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ thirdValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have headerList : headers rows = [identityHeader.header, makeHeader.header, relayHeader.header] := by
    simp only [rows, headers, identityEq, makeEq, relayEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have identityInputIndex : identityHeader.header.slot = identityInput.prepared.index := by
    rw [identityEq]; exact identityPacket.aligned.slot
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have relayIndex : relayHeader.header.slot = observed.relayRow.index :=
    relayHeader.aligned.slot.trans (observed.relayRow.prepared_slot relayHeader.prepared).2
  have relayInputIndex : relayHeader.header.slot = relayInput.prepared.index := by
    rw [relayEq]; exact relayPacket.aligned.slot
  have identityMake : identityHeader.header.slot ≠ makeHeader.header.slot := by
    rw [identityIndex, makeIndex]
    exact observed.identityMake
  have identityMakeInput : identityInput.prepared.index ≠ makeInput.prepared.index := by
    rw [← identityInputIndex, ← makeInputIndex]
    exact identityMake
  have identityRelay : identityHeader.header.slot ≠ relayHeader.header.slot := by
    rw [identityIndex, relayIndex]
    exact observed.identityRelay
  have identityRelayInput : identityInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← identityInputIndex, ← relayInputIndex]
    exact identityRelay
  have makeRelay : makeHeader.header.slot ≠ relayHeader.header.slot := by
    rw [makeIndex, relayIndex]
    exact observed.makeRelay
  have makeRelayInput : makeInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← makeInputIndex, ← relayInputIndex]
    exact makeRelay
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.expression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨identityTerminal, _identityExpression, identitySupport⟩ :=
    identityHeader.identity_support observed receiver (actualStagePrepared fixture)
  obtain ⟨identitySupport⟩ := identitySupport
  obtain ⟨relayTerminal, _relayExpression, relaySupport⟩ :=
    relayHeader.relay_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨relaySupport⟩ := relaySupport
  let property := fun header => Σ terminal : Terminal header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectThree identityMake identityRelay makeRelay property
      ⟨identityTerminal, .recursive identitySupport⟩ ⟨makeTerminal, makeSupport⟩
      ⟨relayTerminal, .canonical relaySupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    makeInput := makeInput
    relayInput := relayInput
    identityRow := identityRow
    makeRow := makeRow
    relayRow := relayRow
    identityPacket := identityPacket
    makePacket := makePacket
    relayPacket := relayPacket
    identityHeader := identityHeader
    makeHeader := makeHeader
    relayHeader := relayHeader
    identityEq := identityEq
    makeEq := makeEq
    relayEq := relayEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [identityMakeInput, identityRelayInput, makeRelayInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family identityHeader makeHeader relayHeader (actualStagePrepared fixture) receiver association
    identityDescriptor := identityHeader.descriptor identityStages
    makeDescriptor := makeHeader.descriptor makeStages
    relayDescriptor := relayHeader.descriptor relayStages }⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
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
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.relayRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

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
    support.relayHeader.header session mapping world heap store caller entries

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
      support.relayHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.relayHeader.header.function.context before source arguments outcome after

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
      support.relayHeader.header.function.context parameter argument packedSource)
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
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
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


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.relayHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, _started, _parameterView, _resultView,
    _succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType input state.atRecipe
      state.registry state.atSession (by simpa only [entryHandle] using call.executed) .skip invocation
  have addedNil : added = [] := by
    simpa only [RecursiveNamedPublicNestedOutputSelections.Selection.handles, List.map_eq_nil_iff] using _handles
  subst added
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
    history := by simpa only [List.append_nil, PublicSupports.functions] using retained }
  exact ⟨sources, source, next, packing, sourceSize, trace⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsRelayStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public relay call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.relay_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.relayRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.relayHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_relay_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.relayHeader.relay_input_types]
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
    exact support.relayDescriptor
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
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
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
  rw [resultType, selected, support.relayHeader.relay_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function .unit .word
    rw [selected]
    exact support.relayHeader.relay_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.relay
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.relayRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.relayHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.relay_typed_handle call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsSeed
/-! Actual initialization and the first public relay(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (relayStages : ObservedStages fixture observed.relayRow)
    (first : ObservedPublicRun fixture observed.relayRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.relayHeader.header
          (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
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
  have selectedEq : selectedHeader = support.relayHeader.header := by
    apply selected_relay_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.relayRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.relayHeader.header.function.context
      (support.relayHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.relayHeader.relay_input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.relayHeader.header support.relayInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.relayPacket.header.named.specialized support.relayInput.prepared.available)) := by
    rw [support.relayEq]
    exact support.relayPacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
      first.started first.executed first.returned support.relayDescriptor
  let entry : Entry := ⟨support.relayHeader.header.function.resultType, source, first.handle,
    payload, support.relayHeader.header.output, runOptions.outputValidationFuel⟩
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
  rw [resultType, support.relayHeader.relay_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.relayHeader.relay_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.relayInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (relayStages : ObservedStages fixture observed.relayRow)
    (first : ObservedPublicRun fixture observed.relayRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.relayHeader.header
          (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle support relayStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsPublicExecution
/-! Three actual nested direct factory calls and three later handle calls keep
all returned sessions and captured Source heaps in one ordered history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  intervening : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, intervening]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, intervening]
  firstTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.relayHeader.header
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    interveningState.heap second.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness relayStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages relayStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope relayStages.sidecar [] support.relayHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support relayStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.relay_typed_handle sequence.second scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.relayHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.relay_typed_handle sequence.intervening scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word interveningState second
    (by simp) secondType secondHandle secondHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstReadState, interveningState, secondReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness relayStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages relayStages sequence receiver⟩

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel closureType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world closureType source payload nativeType

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.relayRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after ∧ ReturnedValue completion returned source outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.relayRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.relayHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.relayHeader.header := by
    apply selected_relay_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.relayRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.relayHeader.header.function.context
      (support.relayHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.relayHeader.relay_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
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
  rw [rawResult, support.relayHeader.relay_result_type] at requested
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  have checkpointReady := started.original.initial_registry.exportsReady (sessionAt.exportsReady_iff.mp initialReady)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld closureType source _payload support.relayHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.relayHeader.relay_result_type] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl, _payload, _, encoded, represented⟩



end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectCallsForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {value : Core.Word}
    (call : ObservedFunctionCall session observed.relayRow.row.key [.word value])
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after ∧
          ReturnedValue completion returned source outputFuel

theorem forward_relay {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.relayRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.relayHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_relay_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.relayHeader.relay_input_types]
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
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
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
  rw [resultType, selectedHeader, support.relayHeader.relay_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session entries := {
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
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld closureType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = closureType := by rw [selectedHeader]; exact support.relayHeader.relay_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl, payload, _, encoded, represented⟩


/-- All three nested-direct factory executions have independent Source-to-public
bounds, at their exact original checkpoints and current captured heaps. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {relayStages : ObservedStages fixture observed.relayRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness relayStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.intervening
    meaning.intervening.source meaning.interveningState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {relayStages : ObservedStages fixture observed.relayRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness relayStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have readReady := sequence.firstRead.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_relay meaning.initial sequence.second firstReady meaning.secondTrace,
    forward_relay meaning.firstReadState sequence.intervening readReady meaning.interveningTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness relayStages sequence receiver, ForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra identityStages makeStages relayStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let identityStages ← observeStages fixture observed.identityRow
  let makeStages ← observeStages fixture observed.makeRow
  let relayStages ← observeStages fixture observed.relayRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra identityStages makeStages relayStages sequence
  IO.println "Nested direct identity/make: relay10/relay20/A10/relay30/B20/A10, exact Source heaps and histories, all three relay public fuel bounds proved"

end Tests.SourceCoreDirectCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
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


structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    where
  makeInput : Input fixture.recipe.compiled
  readInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  readRow : readInput.row = observed.readRow.row
  makePacket : Issued makeInput
  readPacket : Issued readInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  readHeader : ActualHeader fixture observed.readRow.row
  makeEq : makeHeader.header = makePacket.header
  readEq : readHeader.header = readPacket.header
  rows : Inventory [makeInput, readInput]
  rowsEq : rows = .cons makePacket (.cons readPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, readInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  readDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named readHeader.header.named.signature.key)

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    : Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket,
    makeHeader, readHeader, makeEq, readEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, readInput] := .cons makePacket (.cons readPacket .nil)
  have headerList : headers rows = [makeHeader.header, readHeader.header] := by
    simp only [rows, headers, makeEq, readEq]
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have readIndex : readHeader.header.slot = observed.readRow.index :=
    readHeader.aligned.slot.trans (observed.readRow.prepared_slot readHeader.prepared).2
  have slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot := by
    rw [makeIndex, readIndex]
    exact observed.distinctSlots
  have inputDistinct : makeInput.prepared.index ≠ readInput.prepared.index := by
    have left : makeHeader.header.slot = makeInput.prepared.index := by
      rw [makeEq]; exact makePacket.aligned.slot
    have right : readHeader.header.slot = readInput.prepared.index := by
      rw [readEq]; exact readPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  exact ⟨{
    makeInput := makeInput
    readInput := readInput
    makeRow := makeRow
    readRow := readRow
    makePacket := makePacket
    readPacket := readPacket
    makeHeader := makeHeader
    readHeader := readHeader
    makeEq := makeEq
    readEq := readEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    makeDescriptor := makeHeader.descriptor makeStages
    readDescriptor := readHeader.descriptor readStages }⟩

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedProgramCertificate
/-! The original direct issued program is admitted once from its complete actual
cache. A finite row check selects the existing two-header order; it does not
construct syntax, metadata, closure support or method body support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate
  rows : ∀ row ∈ certificate.table.rows, row ∈ [observed.makeRow.row, observed.readRow.row]

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original direct issued program certification rejected")
  | some certificate =>
      if rows : certificate.table.rows.all (fun row =>
          [observed.makeRow.row, observed.readRow.row].any (fun expected => row == expected)) = true then
        pure ⟨certificate, accepted, by
          intro row member
          obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
          exact (eq_of_beq same).symm ▸ present⟩
      else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.readInput] admission.certificate.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeRow⟩
  · exact ⟨inventory.readInput, by simp, inventory.readRow⟩

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue_without_methods fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.makeRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)

/-- This proof is exercised by the same runtime-produced certificate used by
the five-operation regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
abbrev ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) :=
  RecursiveNamedPublicPhysicalSessionState.FunctionCall session key arguments runOptions

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



end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed completion) :
    headers support.rows = [support.makeHeader.header, support.readHeader.header] :=
  by
    rw [support.rowsEq]
    simp only [headers, support.makeEq, support.readEq]

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed makeStages readStages
  obtain ⟨program⟩ := admission.certificate.issue_for_without_methods fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    inventory.rows (admission.aligned inventory)
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)
  exact ⟨{toOrdinaryInventory := inventory, program := program}⟩

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions (headers support.rows)
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
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general observed.profile origin)

abbrev RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) :=
  RecursiveNamedPublicPhysicalSessionState.State support.rows support.makeHeader.header
    receiver.completion observed.profile fixture.recipe publicSession entries

abbrev SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header header
    invocation before arguments outcome after

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse

private theorem statement_roots_injective {left right : List StatementId}
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

private theorem returned_expression
    {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment
      before (id :: rest) finalContext (.returned value) after) :
    Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before
      expression value after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnUnit contains otherForm =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnValue contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact child.sound.value_plain
  | tail contains otherForm _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | discard contains otherForm _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letUninitialized contains otherForm _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letInitialized contains otherForm _ _ _ _ _
  | letGeneralized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | bitNotProjected contains otherForm _ _ _ _ _
  | bitNotBare contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem lambda_shape
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda [] .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ function : Dynamic.Closure,
      value = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw
    exact ⟨_, rfl, rfl, rfl⟩
  | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

/-- The existing public factory meaning fixes the exact returned closure,
including its original captures; no closure-shape observation is assumed. -/
theorem SourceCall.make_closure
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation before [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  have parameters : support.makeHeader.header.function.parameters = [observed.makeShape.binder] := by
    rw [support.makeHeader.header.parameters, ← support.makeHeader.header.inputs,
      support.makeHeader.source, observed.makeShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, _allocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ support.makeHeader.header.unique
  have bodyEq : support.makeHeader.header.function.body = [observed.makeShape.statement.id] := by
    apply statement_roots_injective
    rw [← support.makeHeader.header.agreement.roots, support.makeHeader.source, observed.makeShape.roots]
    rfl
  have statementFound : child.source.lookupStatement? observed.makeShape.statement.id =
      some observed.makeShape.statement := by
    rw [sourceEq, support.makeHeader.source]
    exact observed.makeShape.statementFound
  have expressionFound : child.source.lookupExpression? observed.makeShape.expression.id =
      some observed.makeShape.expression := by
    rw [sourceEq, support.makeHeader.source]
    exact observed.makeShape.expressionFound
  rw [support.makeHeader.make_result_type] at converted
  cases converted
  rw [bodyEq] at body
  exact lambda_shape unique expressionFound observed.makeShape.lambda observed.makeShape.coercions
    (returned_expression unique statementFound observed.makeShape.returnStatement body)

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.makeRow) :
    ObservedFunctionCall first.session observed.makeRow.row.key [.word seed] :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started support.rows fixture.recipePrepared
      support.makeHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.makeHeader support.readHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 100000, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start support
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      support.makeHeader.header.function.context [.word seed] support.makeHeader.header.types := by
    have bindingTypes : support.makeHeader.header.types =
        support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq support.makeHeader.header.extended
      rw [support.makeHeader.header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    rw [bindingTypes, support.makeHeader.make_input_types extra]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function support.rows fixture.recipePrepared
      support.makeHeader.header support.makeHeader.header support.program support.distinct first.as_function_call start
      (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
      inputTypes inputMeanings support.makeDescriptor
      (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded start.atCheckpoint
  have atRecipe : start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := exported.function_source_type requested (valueEq.symm.trans first.returned)
  exact ⟨entry, type.trans support.makeHeader.make_result_type, handle, handleType, state, trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle extra support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedSequence
/-! Genuine named and builtin issuances are interleaved with direct public
calls. Each next operation uses the exact completion of its predecessor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

def issuanceFuel : Nat := 1024
def builtinArgument : Int := 37
def builtinResult : Core.Word := Core.Word.ofNatModulo 37

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.BuiltinIssuedAt .wordFromInteger issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

def observeBuiltin {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) : IO (ObservedBuiltin session) := do
  match ← session.builtinWithReceipt .wordFromInteger issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "builtin issuance did not return a function")

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

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  named : ObservedNamed first.completion.session observed.readRow.row.key
  read : ObservedInvocation named.completion.session named.handle (.function first.handle)
  readValue : read.completion.value = .word seed
  builtin : ObservedBuiltin read.completion.session
  converted : ObservedInvocation builtin.completion.session builtin.handle (.integer builtinArgument)
  convertedValue : converted.completion.value = .word builtinResult

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let named ← observeNamed first.completion.session observed.readRow.row.key
  let read ← observeInvocation named.completion.session named.handle (.function first.handle)
  let ⟨readValue⟩ ← confirm (read.completion.value = .word seed) "direct named read did not return 10"
  let builtin ← observeBuiltin read.completion.session
  let converted ← observeInvocation builtin.completion.session builtin.handle (.integer builtinArgument)
  let ⟨convertedValue⟩ ← confirm (converted.completion.value = .word builtinResult)
    "direct builtin conversion did not return 37"
  pure ⟨first, named, read, readValue, builtin, converted, convertedValue⟩

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedIssuance
/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

theorem read_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.readPacket.header.named.specialized.function.type = .function (.function .unit .word) .word := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.readPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.readPacket.header.named.specialized.function.type = _ at shape
  rw [← support.readPacket.sourceAt.frame.result, ← support.readEq,
    support.readHeader.read_types, support.readHeader.read_result_type] at shape
  rw [support.readEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

/-- Named issuance appends the compiler-selected read global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.readRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function (.function .unit .word) .word ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function (.function .unit .word) .word ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.readPacket support.rows := by
    rw [support.rowsEq]
    exact .tail _ (.here _)
  have issued : publicSession.NamedIssuedAt support.readPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.readEq, support.readHeader.key]
    exact call.issued
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named support.program
      fixture.recipePrepared state support.readPacket member issued call.returned
  exact ⟨entry, sourceType.trans (read_source_type support), handle,
    handleType.trans (read_source_type support), source, next, heap⟩

/-- Builtin issuance appends the actual closed wordFromInteger payload. -/
theorem remember_builtin (state : RetainedState support publicSession entries)
    (call : ObservedBuiltin publicSession) :
    ∃ entry : Entry,
      entry.sourceType = .function .integer .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .integer .word ∧ entry.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  obtain ⟨entry, sourceType, source, handle, handleType, next, heap⟩ :=
    RecursiveNamedPublicPhysicalSessionIssuance.State.remember_builtin fixture.recipePrepared
      state .wordFromInteger call.issued call.returned
  exact ⟨entry, sourceType, handle, handleType, source, next, heap⟩

end State
end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedInvocation
/-! The same public proof consumes actual named and builtin handles. Argument
and callee representations are derived from their current retained history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source argument : Dynamic.Value)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source [argument] (.value (.word word)) after

/-- Exact observed public completion fixes the Source result; structural input
receipts and the actual packed encoder fix the Source argument. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (_simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (singleton : ∀ sources, Dynamic.ValuesPack sources source → sources = [source])
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source source word after.heap := by
  obtain ⟨sources, packing, _arity, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar support.program
      fixture.recipePrepared state entry member (.word word) entryType
      (entryHandle ▸ handleType) input (by simpa only [entryHandle] using call.executed)
      returned invocation
  exact ⟨next, size, singleton sources packing ▸ trace⟩


end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedPublicExecution
/-! Actual named and builtin public invocation is connected to independent
Source execution across the same reached session and retained function history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named builtin : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function (.function .unit .word) .word ∧
      builtin.sourceType = .function .integer .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      builtin.handle = sequence.builtin.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      builtin.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ readState : RetainedState support sequence.read.completion.session [first, named],
      ∃ builtinState : RetainedState support sequence.builtin.completion.session [first, named, builtin],
      ∃ finalState : RetainedState support sequence.converted.completion.session [first, named, builtin],
        namedState.heap = firstState.heap ∧ builtinState.heap = readState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceInvocation support scope namedState.heap named.source first.source seed readState.heap ∧
        SourceInvocation support scope builtinState.heap builtin.source (.integer builtinArgument)
          builtinResult finalState.heap

/-- The compiler/checker observations and the actual IO calls discharge every
static, input, capture and public continuation premise for this sequence. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed admission makeStages readStages receiver
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, _firstHandleType, firstState, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, _firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨named, namedType, namedHandle, namedHandleType, namedSource, namedState, namedHeap⟩ :=
    remember_named firstState sequence.named
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named]
      support.makeHeader.header.function.context (.function .unit .word)
      (.function sequence.first.handle) first.source := by
    simpa only [firstType, firstHandle] using
      (RecursiveNamedPublicFunctionHistoryInputs.Input.retained
        (context := support.makeHeader.header.function.context) first (by simp : first ∈ [first, named]))
  obtain ⟨readState, readTrace⟩ := invoke namedState named (by simp) namedType namedHandle namedHandleType
    input (.function sequence.first.handle)
    (by intro sources packing; rw [firstSource] at packing ⊢; cases packing; rfl)
    sequence.read sequence.readValue scope
  obtain ⟨builtin, builtinType, builtinHandle, builtinHandleType, builtinSource, builtinState, builtinHeap⟩ :=
    remember_builtin readState sequence.builtin
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named, builtin]
      support.makeHeader.header.function.context .integer (.integer builtinArgument) (.integer builtinArgument) :=
    .data ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
      ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
  obtain ⟨finalState, finalTrace⟩ := invoke builtinState builtin (by simp) builtinType builtinHandle builtinHandleType
    integerInput (.simple (.integer builtinArgument))
    (by intro sources packing; cases packing; rfl) sequence.converted sequence.convertedValue scope
  exact ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning : ∃ receiver : ObservedReceiver fixture observed, SequenceMeaning makeStages sequence receiver := by
    obtain ⟨receiver⟩ := initial_receiver fixture observed
    exact ⟨receiver, sequence_meaning fixture observed extra admission makeStages readStages sequence receiver⟩
  IO.println "Actual direct issued calls: named read of captured 10 and builtin conversion 37, Source arguments/results and current histories proved"

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectIssuedForward
/-! The actual two packed calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) (word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value} {word : Core.Word}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (_simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (call : ObservedInvocation publicSession handle argument)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source source word after) :
    ForwardWordAt support publicSession entries handle argument word after := by
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨size, trace⟩ := trace
  refine ⟨publicCheckpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectWordForward.forward_call support.program
    fixture.recipePrepared state entry member word entryType input
    (by simpa only [entryHandle] using accepted) (.singleton source) trace


def ForwardSequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named builtin : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function (.function .unit .word) .word ∧
      builtin.sourceType = .function .integer .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      builtin.handle = sequence.builtin.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      builtin.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ readState : RetainedState support sequence.read.completion.session [first, named],
      ∃ builtinState : RetainedState support sequence.builtin.completion.session [first, named, builtin],
      ∃ finalState : RetainedState support sequence.converted.completion.session [first, named, builtin],
        namedState.heap = firstState.heap ∧ builtinState.heap = readState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceInvocation support scope namedState.heap named.source first.source seed readState.heap ∧
        SourceInvocation support scope builtinState.heap builtin.source (.integer builtinArgument)
          builtinResult finalState.heap ∧
        ForwardWordAt support sequence.named.completion.session [first, named] sequence.named.handle
          (.function sequence.first.handle) seed readState.heap ∧
        ForwardWordAt support sequence.builtin.completion.session [first, named, builtin] sequence.builtin.handle
          (.integer builtinArgument) builtinResult finalState.heap

/-- The real named and builtin calls establish independent Source traces,
then prove public success for all sufficient fuel on those same checkpoints. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ForwardSequenceMeaning makeStages sequence receiver := by
  obtain ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace⟩ := sequence_meaning fixture observed extra admission makeStages readStages sequence receiver
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named]
      support.makeHeader.header.function.context (.function .unit .word)
      (.function sequence.first.handle) first.source := by
    simpa only [firstType, firstHandle] using
      (RecursiveNamedPublicFunctionHistoryInputs.Input.retained
        (context := support.makeHeader.header.function.context) first (by simp : first ∈ [first, named]))
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named, builtin]
      support.makeHeader.header.function.context .integer (.integer builtinArgument) (.integer builtinArgument) :=
    .data ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
      ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
  exact ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace,
    forward_word namedState named (by simp) namedType namedHandle input (.function sequence.first.handle)
      sequence.read readTrace,
    forward_word builtinState builtin (by simp) builtinType builtinHandle integerInput (.simple (.integer builtinArgument))
      sequence.converted finalTrace⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning : ∃ receiver : ObservedReceiver fixture observed, ForwardSequenceMeaning makeStages sequence receiver := by
    obtain ⟨receiver⟩ := initial_receiver fixture observed
    exact ⟨receiver, sequence_forward_meaning fixture observed extra admission makeStages readStages sequence receiver⟩
  IO.println "Actual direct named and builtin calls: Source reflection and public Word preservation with output fuel 1 proved"

end Tests.SourceCoreDirectIssued
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectOutputSequence
/-! A direct named factory call exports a second capture, which is then reused
through its actual returned session alongside the original capture. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

structure ObservedFunctionInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    extends Tests.SourceCoreDirectIssued.ObservedInvocation session handle (.word secondSeed) where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedFunctionInvocation session handle) := do
  let call ← Tests.SourceCoreDirectIssued.observeInvocation session handle (.word secondSeed)
  match returned : call.completion.value with
  | .function exported => pure ⟨call, exported, returned⟩
  | _ => throw (IO.userError "direct factory did not return a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  named : Tests.SourceCoreDirectIssued.ObservedNamed first.completion.session observed.makeRow.row.key
  second : ObservedFunctionInvocation named.completion.session named.handle
  distinct : first.handle ≠ second.handle
  invokeFirst : Tests.SourceCoreCapturedDirect.ObservedInvocation second.completion.session first.handle
  firstValue : invokeFirst.completion.value = .word seed
  invokeSecond : Tests.SourceCoreCapturedDirect.ObservedInvocation invokeFirst.completion.session second.handle
  secondValue : invokeSecond.completion.value = .word secondSeed
  invokeFirstAgain : Tests.SourceCoreCapturedDirect.ObservedInvocation invokeSecond.completion.session first.handle
  firstValueAgain : invokeFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let named ← Tests.SourceCoreDirectIssued.observeNamed first.completion.session observed.makeRow.row.key
  let second ← observeFunctionInvocation named.completion.session named.handle
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "direct factory reused the original captured handle"
  let invokeFirst ← Tests.SourceCoreCapturedDirect.observeInvocation second.completion.session first.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "original capture did not return 10"
  let invokeSecond ← Tests.SourceCoreCapturedDirect.observeInvocation invokeFirst.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "direct factory capture did not return 20"
  let invokeFirstAgain ← Tests.SourceCoreCapturedDirect.observeInvocation invokeSecond.completion.session first.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "original capture changed after reuse"
  pure ⟨first, named, second, distinct, invokeFirst, firstValue, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩

end Tests.SourceCoreDirectOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectOutputIssuance
/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open Tests.SourceCoreDirectIssued (ObservedNamed issuanceFuel)
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

private theorem indexed_artifact_eq
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {leftArtifact rightArtifact : SourceCoreIndexedSession.Artifact}
    {left : SourceCoreIndexedSession.Session leftArtifact} {right : SourceCoreIndexedSession.Session rightArtifact}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : leftArtifact = rightArtifact := by
  rcases artifact with ⟨compilation, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected native atRecipe =>
      cases session
      exact first.1.symm.trans second.1

private theorem make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.makeHeader.header.types = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) support.makeHeader).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← support.makeHeader.source, support.makeHeader.header.inputs] at raw
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq support.makeHeader.header.extended
  rw [support.makeHeader.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at raw types
  exact types.symm.trans raw

theorem make_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.makePacket.header.named.specialized.function.type = .function .word (.function .unit .word) := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.makePacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.makePacket.header.named.specialized.function.type = _ at shape
  rw [← support.makePacket.sourceAt.frame.result, ← support.makeEq,
    make_types support, support.makeHeader.make_result_type] at shape
  rw [support.makeEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

private theorem named_handle_type (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.makeRow.row.key) :
    call.handle.sourceType = .function .word (.function .unit .word) := by
  obtain ⟨artifact, before, actual, beforeAt, issued, completedAt⟩ := call.issued
  cases indexed_artifact_eq state.atSession beforeAt
  have actualType := issued.function_source_type (completedAt.1.symm.trans call.returned)
  obtain ⟨expected, native, _same, sourceType, _fuel, _encoded, factory⟩ := issued.receipt
  have actualFactory : fixture.recipe.NamedCallableAt observed.makeRow.row.key expected native := by
    have atRecipe := state.atRecipe
    cases artifactEq : state.artifact
    rename_i authority actualRecipe
    rw [artifactEq] at atRecipe factory
    change actualRecipe = fixture.recipe at atRecipe
    cases atRecipe
    exact factory
  have keyEq : observed.makeRow.row.key = support.makePacket.header.named.signature.key :=
    support.makeHeader.key.symm.trans (congrArg (fun header => header.named.signature.key) support.makeEq)
  rw [keyEq] at actualFactory
  obtain ⟨signature, index, specialized, location, closure, identity, descriptor,
    _global, _key, record, expectedType, _remaining⟩ := actualFactory.prepared fixture.recipePrepared
  have specializedEq := Except.ok.inj
    (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record _ support.makePacket.header))
  subst specialized
  exact actualType.trans (sourceType.trans (expectedType.trans (make_source_type support)))

/-- Named issuance appends the compiler-selected make global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.makeRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function .word (.function .unit .word) ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function .word (.function .unit .word) ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.makePacket.header.named.specialized support.makeInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.makePacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.makePacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.makeEq, support.makeHeader.key]
    exact call.issued
  obtain ⟨actual, native, actualAt, retained⟩ := RecursiveNamedPublicHistoryIssuance.named_remembered
    fixture.recipePrepared [support.makeInput, support.readInput] support.rows support.makePacket member
    receiver.completion.result.context.registry receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile state.history state.atRecipe state.atSession issued call.returned fixture.source_wellFormed
  have registry := (call.issued.same_runtime.indexed state.atSession actualAt.2.2.2).registry_at state.registry
  let entry : Entry := ⟨support.makePacket.header.named.specialized.function.type,
    .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.makePacket.header.named.specialized support.makeInput.prepared.available)), call.handle, native,
    Core.CallableContract.functionType support.makePacket.header.named.signature.parameterType
      support.makePacket.header.named.signature.resultType, issuanceFuel⟩
  refine ⟨entry, make_source_type support, rfl, named_handle_type state call, rfl,
    ⟨state.artifact, actual.session, state.mapping, state.world, state.heap, state.store, state.caller,
      actualAt.2.2.2, state.atRecipe, registry, retained⟩, rfl⟩

end State
end Tests.SourceCoreDirectOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectOutputFactory
/-! A directly invoked factory's actual exported function is collected into
its current history, retaining the Source value from that same call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

private theorem selected_function {raw : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (same.symm ▸ (Selection.function (type := raw))) source native nativeType fuel entries) :
    entries = [⟨raw, source, handle, native, nativeType, fuel⟩] := by
  cases same
  cases selected
  rfl

/-- The returned singleton is taken from the genuine codec selection and
successful Source trace; its capture is never reconstructed from a new run. -/
theorem invoke_factory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (named : Entry) (member : named ∈ entries)
    (namedType : named.sourceType = .function .word (.function .unit .word))
    (namedSource : named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.makePacket.header.named.specialized support.makeInput.prepared.available)))
    {handle : SourceCorePublicValues.Handle} (namedHandle : named.handle = handle)
    (handleType : handle.sourceType = .function .word (.function .unit .word))
    (call : ObservedFunctionInvocation publicSession handle) (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word secondSeed]
          (.value entry.source) next.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  let selection : Selection (.function .unit .word) call.completion.value :=
    call.returned.symm ▸ Selection.function
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source,
      payload, after, finalMap, finalWorld, reached, added, started, _parameterView, _resultView,
      succeeded, actualAt, packing, trace, result, nativeValue, selected, _handles, _related,
      retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallableOutputHistory.public_invoke_succeeded_collects_function_tree
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := named) (member := member) (entryType := namedType)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.word secondSeed))
      state.atSession (by simpa only [namedHandle] using call.executed) selection invocation
  have handleType : named.handle.sourceType = .function .word (.function .unit .word) := namedHandle ▸ handleType
  have requested := started.requested_exact handleType
  have returnedType := succeeded.function_source_type requested (actualAt.1.symm.trans call.returned)
  have sourcesEq : sources = [.word secondSeed] := by cases packing; rfl
  have addedEq := selected_function call.returned selected
  rw [addedEq] at retained
  let entry : Entry := ⟨.function .unit .word, source, call.handle, payload, nativeResult,
    runOptions.outputValidationFuel⟩
  let next : RetainedState support call.completion.session (entries ++ [entry]) :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨entry, rfl, rfl, returnedType, next, support.makeInput.prepared.available,
    CallableNamedReversal.global (CallableNamedMetadata.global
      support.makePacket.header.named.specialized support.makeInput.prepared.available), sourceSize, ?_, ?_⟩
  · rw [support.makeEq]
    exact support.makePacket.sourceAt
  · simpa only [namedSource, sourcesEq] using trace

end Tests.SourceCoreDirectOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectOutputPublicExecution
/-! A direct named factory export becomes a later direct-call input, preserving
both the new capture and the earlier capture through intervening executions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named second : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function .word (.function .unit .word) ∧
      second.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      second.handle = sequence.second.handle ∧ first.handle ≠ second.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.makePacket.header.named.specialized support.makeInput.prepared.available)) ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, named, second],
      ∃ firstInvokedState : RetainedState support sequence.invokeFirst.completion.session [first, named, second],
      ∃ secondInvokedState : RetainedState support sequence.invokeSecond.completion.session [first, named, second],
      ∃ finalState : RetainedState support sequence.invokeFirstAgain.completion.session [first, named, second],
        namedState.heap = firstState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.makeHeader.header scope namedState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope secondState.heap first.source
          (.value (.word seed)) firstInvokedState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope firstInvokedState.heap second.source
          (.value (.word secondSeed)) secondInvokedState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope secondInvokedState.heap first.source
          (.value (.word seed)) finalState.heap

/-- The real public output encoder supplies the newly remembered entry, which
is reused with the original capture in the actual returned sessions. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, firstState, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨named, namedType, namedHandle, namedHandleType, namedSource, namedState, namedHeap⟩ :=
    remember_named firstState sequence.named
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    invoke_factory namedState named (by simp) namedType namedSource namedHandle namedHandleType sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨firstInvokedState, firstInvokedTrace⟩ := Tests.SourceCoreCapturedDirect.invoke secondState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirst sequence.firstValue scope
  obtain ⟨secondInvokedState, secondInvokedTrace⟩ := Tests.SourceCoreCapturedDirect.invoke firstInvokedState second (by simp)
    secondType secondSource secondParameters secondHandle secondHandleType sequence.invokeSecond sequence.secondValue scope
  obtain ⟨finalState, finalTrace⟩ := Tests.SourceCoreCapturedDirect.invoke secondInvokedState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirstAgain sequence.firstValueAgain scope
  refine ⟨support, first, named, second, firstType, namedType, secondType,
    firstHandle, namedHandle, secondHandle, ?_, namedSource,
    firstState, namedState, secondState, firstInvokedState, secondInvokedState, finalState,
    namedHeap, firstTrace, secondTrace, firstInvokedTrace, secondInvokedTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct factory output: collected make(20), reused captures 10/20/10, Source arguments/results and returned histories proved"

end Tests.SourceCoreDirectOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFunctionForward
/-! Genuine issuer receipts close function-output preservation on the actual
direct make(20) checkpoint. The same runtime scenario reuses captures 10/20/10. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFunctionForward
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse Tests.SourceCoreDirectOutput
open RecursiveNamedPublicFunctionHistory (Entry)

private def observeOwnedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO { first : ObservedPublicRun fixture observed // first.bootstrap.ExportAuthorityAt } := do
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
          return ⟨⟨opened.val, opened.property, fresh.val, fresh.property.1, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩, fresh.property.2⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedForwardSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  sequence : Tests.SourceCoreDirectOutput.ObservedSequence fixture observed
  authority : sequence.first.bootstrap.ExportAuthorityAt

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeForwardSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedForwardSequence fixture observed) := do
  let first ← observeOwnedPublicRun fixture observed.makeRow
  let named ← Tests.SourceCoreDirectIssued.observeNamed first.val.completion.session observed.makeRow.row.key
  let second ← observeFunctionInvocation named.completion.session named.handle
  let ⟨distinct⟩ ← confirm (first.val.handle ≠ second.handle) "direct factory reused the original captured handle"
  let invokeFirst ← Tests.SourceCoreCapturedDirect.observeInvocation second.completion.session first.val.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "original capture did not return 10"
  let invokeSecond ← Tests.SourceCoreCapturedDirect.observeInvocation invokeFirst.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "direct factory capture did not return 20"
  let invokeFirstAgain ← Tests.SourceCoreCapturedDirect.observeInvocation invokeSecond.completion.session first.val.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "original capture changed after reuse"
  pure ⟨⟨first.val, named, second, distinct, invokeFirst, firstValue, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩, first.property⟩

/-- All future resumes use the actual original checkpoint. The new function
joins the retained collection at the exact independently established heap. -/
def ForwardFunctionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.word secondSeed) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ source after required,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (exported : Entry),
          outcome = .succeeded completion ∧ completion.value = .function exported.handle ∧
          exported.sourceType = .function .unit .word ∧ exported.source = source ∧
          completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session (entries ++ [exported]), returned.heap = after

private theorem forward_function {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function .word (.function .unit .word))
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (call : ObservedFunctionInvocation publicSession handle)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ForwardFunctionAt support publicSession entries handle := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  let selection : RecursiveNamedPublicOutputSelections.Selection (.function .unit .word) call.completion.value :=
    call.returned.symm ▸ .function
  obtain ⟨_checkpoint, _actual, _generation, _value, _finalStore, _actualParameter, _actualResult,
      _nativeParameter, _nativeResult, _callable, _packed, _encodedValues, sources, sourceSize, source,
      _payload, after, _finalMap, _finalWorld, _reached, _added, _started, _parameterView, _resultView,
      _succeeded, _actualAt, packing, trace, _result, _nativeValue, _selected, _handles, _related,
      _retained, _encodedRegistry, _returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallableOutputHistory.public_invoke_succeeded_collects_function_tree
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.word secondSeed))
      state.atSession (by simpa only [entryHandle] using call.executed) selection invocation
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have registryEq := started.function_tree_registry (.simple (.word secondSeed)) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  rw [← entryHandle] at started
  obtain ⟨required, payload, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectCallableFunctionPreservation.public_resume_has_sufficient_fuel
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (input := input)
      (state.atSession.exportsReady_iff.mp exportsReady) started metadata packing trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, source, after, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, handle, reached, succeeded, handleValue, _sourceType, _exported,
      indexedAt, _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  let exported : Entry := ⟨.function .unit .word, source, handle, payload, nativeResult, outputFuel⟩
  exact ⟨publicCompletion, exported, succeeded, handleValue, rfl, rfl,
    indexedAt.2.2.2.exportsReady_iff.mpr returnedReady,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

/-- The rich initial receipt is obtained from the actual bootstrap operation;
all later export readiness follows the real first run and named issuance. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (observedSequence : ObservedForwardSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Tests.SourceCoreDirectOutput.SequenceMeaning makeStages observedSequence.sequence receiver ∧
    ∃ (support : PublicSupports receiver) (first named : Entry),
      ForwardFunctionAt support observedSequence.sequence.named.completion.session [first, named]
        observedSequence.sequence.named.handle := by
  have meaning := Tests.SourceCoreDirectOutput.sequence_meaning fixture observed extra makeStages readStages
    observedSequence.sequence receiver
  refine ⟨meaning, ?_⟩
  obtain ⟨support, first, named, second, _firstType, namedType, _secondType,
    _firstHandle, namedHandle, _secondHandle, _distinct, _namedSource,
    _firstState, namedState, _secondState, _firstInvoked, _secondInvoked, _finalState, _posts⟩ := meaning
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single observedSequence.sequence.first.ready).exportsReady
    observedSequence.authority
  have firstReady := observedSequence.sequence.first.executed.exportsReady initialReady
  have namedReady := observedSequence.sequence.named.issued.exportsReady firstReady
  exact ⟨support, first, named,
    forward_function namedState named (by simp) namedType namedHandle observedSequence.sequence.second namedReady
      (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeForwardSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct factory: Source implies function export with output fuel 1 and reusable History; captures 10/20/10 retained"

end Tests.SourceCoreDirectFunctionForward
end
