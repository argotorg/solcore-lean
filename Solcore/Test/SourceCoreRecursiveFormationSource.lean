import Solcore.Test.SourceCoreRecursiveIndexSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev DirectCall := Tests.SourceCoreRecursiveIndex.DirectCall
abbrev IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :=
  Tests.SourceCoreRecursiveIndex.IdentityShape function signature .word
abbrev closureType : TypeSystem.Ty := .function .unit .word
abbrev factoryType : TypeSystem.Ty := .product closureType closureType
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


structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  call : DirectCall function.typedBody identity read.node.id .word .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = .word

def RelayShape.nodeList {function signature identity} (shape : RelayShape function signature identity) : List SourceInference.Node :=
  [.expression shape.read.node, .expression shape.call.callee.node, .expression shape.call.value.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let returned : StatementFacts := {type:=.word, hasValue:=true, sawReturn:=true, control:=.returned}
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
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have called := shape.call.typed (fields ▸ identityMember) word read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm called shape.statementType)⟩

structure LambdaShape (function : CheckedFunction) (identity : ProgramFunctionSignature) (binder : TypedBinder) where
  read : Read function.typedBody binder .word
  call : DirectCall function.typedBody identity read.node.id .word .word
  innerReturn : StatementNode
  expression : ExpressionNode
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some call.value.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = closureType
  expressionType : expression.type = closureType
  requirements : expression.requirements = []
  coercions : expression.coercions = []

def LambdaShape.nodeList {function identity binder} (shape : LambdaShape function identity binder) : List SourceInference.Node :=
  [.expression shape.read.node, .expression shape.call.callee.node, .expression shape.call.value.node,
   .statement shape.innerReturn, .expression shape.expression]

structure FactoryShape (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody relay initialRead.node.id .word .word
  left : LambdaShape function identity localBinder
  right : LambdaShape function identity localBinder
  initialized : StatementNode
  tupleNode : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType, closureType]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  localOrdinary : localBinder.comptime = false
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some initial.value.node.id)
  initializedType : initialized.type = .unit
  tupleFound : function.typedBody.lookupExpression? tupleNode.id = some tupleNode
  tupleForm : tupleNode.form = .tuple [left.expression.id, right.expression.id]
  tupleRaw : tupleNode.rawType = factoryType
  tupleType : tupleNode.type = factoryType
  tupleRequirements : tupleNode.requirements = []
  tupleCoercions : tupleNode.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  returnStatement : statement.form = .returnStmt (some tupleNode.id)
  statementType : statement.type = factoryType

def FactoryShape.nodeList {function signature identity relay} (shape : FactoryShape function signature identity relay) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
   .statement shape.initialized] ++ shape.left.nodeList ++ shape.right.nodeList ++
   [.expression shape.tupleNode, .statement shape.statement]

theorem FactoryShape.statementTyping {function signature identity relay}
    (shape : FactoryShape function signature identity relay) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (relayMember : relay ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  let returned : StatementFacts := {type:=factoryType, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton returned), rfl, ?_⟩
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
    have initial := shape.initial.typed (fields ▸ relayMember) word initialRead
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible locals closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have lambdaTyped (lambda : LambdaShape function identity shape.localBinder) :
        ExpressionHasType function.typedBody locals lambda.expression.id closureType := by
      have read := lambda.read.typed shape.localScheme shape.localRequirements localWord
        localExtended.local_self localExtended.local_scheme_requirements_self
      have called := lambda.call.typed (show identity ∈ locals.signatures.functions from fields ▸ identityMember) localWord read
      rw [← lambda.expressionType]
      refine .intro (lookupExpression?_sound lambda.expressionFound)
        (lambda.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound lambda.innerReturnFound)
            lambda.innerReturnForm called lambda.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) lambda.expressionRaw callable (lambda.expressionType ▸ callable) ?_
      rw [lambda.requirements, lambda.coercions, lambda.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have pair : TypeAdmissible locals factoryType :=
      ⟨binders, .product (.function (.builtin .unit) (.builtin .word)) (.function (.builtin .unit) (.builtin .word))⟩
    have expressionTyped : ExpressionHasType function.typedBody locals shape.tupleNode.id factoryType := by
      rw [← shape.tupleType]
      refine .intro (lookupExpression?_sound shape.tupleFound)
        (shape.tupleForm ▸ ExpressionFormHasRawType.tuple (.cons (lambdaTyped shape.left) (.cons (lambdaTyped shape.right) (.nil _))))
        shape.tupleRaw pair (shape.tupleType ▸ pair) ?_
      rw [shape.tupleRequirements, shape.tupleCoercions, shape.tupleType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initialized : StatementHasType function.typedBody ⟨factoryType,0⟩ lexical shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initialized (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType))⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) : IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression readNode, .expression callee, .expression value, .statement statement] := function.typedBody.nodes | throw (IO.userError "relay nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let call ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity read.node.id callee value .word .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "formation parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "formation inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "formation returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "formation inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "formation binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "formation roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "formation statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "formation statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "formation statementType"
  return {binder, read, call, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, statementFound, statementForm, statementType}

def observeLambda (function : CheckedFunction) (identity : ProgramFunctionSignature) (binder : TypedBinder)
    (readNode callee value : ExpressionNode) (innerReturn : StatementNode) (expression : ExpressionNode) :
    IO (LambdaShape function identity binder) := do
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let call ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity read.node.id callee value .word .word
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "formation innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some call.value.node.id)) "formation innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "formation innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "formation expressionFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "formation lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType) "formation expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = closureType) "formation expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "formation requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "formation coercions"
  return {
    read := read
    call := call
    innerReturn := innerReturn
    expression := expression
    innerReturnFound := innerReturnFound
    innerReturnForm := innerReturnForm
    innerReturnType := innerReturnType
    expressionFound := expressionFound
    lambda := lambda
    expressionRaw := expressionRaw
    expressionType := expressionType
    requirements := requirements
    coercions := coercions
  }

def observeFactory (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) : IO (FactoryShape function signature identity relay) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "make inputs")
  let [.expression initialReadNode, .expression initialCallee, .expression initialValue, .statement initialized, .expression leftRead, .expression leftCallee, .expression leftValue, .statement leftReturn, .expression leftExpression, .expression rightRead, .expression rightCallee, .expression rightValue, .statement rightReturn, .expression rightExpression, .expression tupleNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "make nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "make local")



  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder initialReadNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay initialRead.node.id initialCallee initialValue .word .word
  let left ← observeLambda function identity localBinder leftRead leftCallee leftValue leftReturn leftExpression
  let right ← observeLambda function identity localBinder rightRead rightCallee rightValue rightReturn rightExpression
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "formation parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "formation inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType, closureType]) "formation returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "formation inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "formation binderRequirements"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "formation localScheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "formation localRequirements"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "formation localOwner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "formation localDistinct"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "formation localOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "formation roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "formation initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initial.value.node.id)) "formation initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "formation initializedType"
  let ⟨tupleFound⟩ ← observed (function.typedBody.lookupExpression? tupleNode.id = some tupleNode) "factory tuple found"
  let ⟨tupleForm⟩ ← observed (tupleNode.form = .tuple [left.expression.id, right.expression.id]) "factory tuple form"
  let ⟨tupleRaw⟩ ← observed (tupleNode.rawType = factoryType) "factory tuple raw type"
  let ⟨tupleType⟩ ← observed (tupleNode.type = factoryType) "factory tuple type"
  let ⟨tupleRequirements⟩ ← observed (tupleNode.requirements = []) "factory tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tupleNode.coercions = []) "factory tuple coercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "formation statementFound"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some tupleNode.id)) "formation returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = factoryType) "formation statementType"
  return {
    binder := binder
    localBinder := localBinder
    initialRead := initialRead
    initial := initial
    left := left
    right := right
    initialized := initialized
    tupleNode := tupleNode
    statement := statement
    parameters := parameters
    inputTypes := inputTypes
    returns := returns
    inputs := inputs
    binderRequirements := binderRequirements
    localScheme := localScheme
    localRequirements := localRequirements
    localOwner := localOwner
    localDistinct := localDistinct
    localOrdinary := localOrdinary
    roots := roots
    initializedFound := initializedFound
    initializedForm := initializedForm
    initializedType := initializedType
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRaw := tupleRaw
    tupleType := tupleType
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    statementFound := statementFound
    returnStatement := returnStatement
    statementType := statementType
  }

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function relay(value: Word) returns (Word) { return identity(value); } function make(seed: Word) returns (function() returns (Word), function() returns (Word)) { let saved: Word = relay(seed); return (lam() { return identity(saved); }, lam() { return identity(saved); }); }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, relayFunction, makeFunction]
  signatures : program.signatures.functions = [identitySignature, relaySignature, makeSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  relayMake : relaySignature.id ≠ makeSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  relayShape : RelayShape relayFunction relaySignature identitySignature
  makeShape : FactoryShape makeFunction makeSignature identitySignature relaySignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, relayFunction, makeFunction], [identitySignature, relaySignature, makeSignature] =>
      let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityFunction identitySignature .word
      let relayShape ← observeRelay relayFunction relaySignature identitySignature
      let makeShape ← observeFactory makeFunction makeSignature identitySignature relaySignature
      let ⟨methods⟩ ← observed (program.methods = []) "scoped methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "identityRelay"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "identityMake"
      let ⟨relayMake⟩ ← observed (relaySignature.id ≠ makeSignature.id) "relayMake"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity nodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures])
          · exact False.elim (relayMake (relayDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact False.elim (relayMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction, relayFunction, makeFunction, identitySignature, relaySignature, makeSignature, functions, signatures, methods, identityDeclaration, relayDeclaration, makeDeclaration, identityRelay, identityMake, relayMake, identityShape, relayShape, makeShape, identityNodes, relayNodes, makeNodes }
    | _, _ => throw (IO.userError "scoped declaration count")

end Tests.SourceCoreRecursiveFormation
