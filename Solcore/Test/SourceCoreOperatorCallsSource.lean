import Solcore.Test.SourceCoreNamedBranchSource

/-! Independent declarative typing of a real checked conditional whose selected
arithmetic operands invoke an imported function. All nodes and call metadata
are observed from the original checker result. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
def functionType : TypeSystem.Ty := .function .word .word

structure TypedNode (source : TypedSource) (expected : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  raw : node.rawType = expected
  type : node.type = expected
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem TypedNode.ordinary {source : TypedSource} {expected : TypeSystem.Ty}
    (node : TypedNode source expected) {context : SourceSemantics.Context}
    (admissible : TypeAdmissible context expected)
    (form : ExpressionFormHasRawType source context node.node.form expected (.ordinary [])) :
    ExpressionHasType source context node.node.id expected := by
  have typed : ExpressionHasType source context node.node.id node.node.type := by
    refine .intro (lookupExpression?_sound node.found) form node.raw admissible (node.type.symm ▸ admissible) ?_
    rw [node.requirements, node.coercions, node.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context node.node.id type) node.type) typed

structure Call (source : TypedSource) (callee argument : ExpressionId) extends TypedNode source .word where
  metadata : IndirectCallResolution
  form : node.form = .call callee [argument] (.indirect metadata)
  application : metadata = ⟨1, .word, .word, []⟩

theorem Call.typed {source : TypedSource} {callee argument : ExpressionId}
    (call : Call source callee argument) {context : SourceSemantics.Context}
    (word : TypeAdmissible context .word)
    (calleeTyped : ExpressionHasType source context callee functionType)
    (argumentTyped : ExpressionHasType source context argument .word) :
    ExpressionHasType source context call.node.id .word := by
  have application : IndirectApplicationValid context call.metadata [.word] .word := by
    rw [call.application]
    exact .intro rfl rfl rfl (.nil _)
  have typed : ExpressionHasType source context call.node.id call.node.type := by
    refine .intro (lookupExpression?_sound call.found)
      (call.form ▸ ExpressionFormHasRawType.indirectCall calleeTyped (.cons argumentTyped (.nil _)) application)
      call.raw word (call.type.symm ▸ word) ?_
    rw [call.requirements, call.coercions, call.type, call.application]
    exact .indirectCall (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.node.id type) call.type) typed

structure IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  statement : StatementNode
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = .word

structure SelectShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  callable : TypedBinder
  flag : TypedBinder
  argument : TypedBinder
  flagRead : Read function.typedBody flag .bool
  negation : TypedNode function.typedBody .bool
  negationForm : negation.node.form = .unary .logicalNot flagRead.node.id
  leftArgument : Read function.typedBody argument .word
  leftFunction : Read function.typedBody callable functionType
  leftCall : Call function.typedBody leftFunction.node.id leftArgument.node.id
  leftValue : Read function.typedBody argument .word
  sum : TypedNode function.typedBody .word
  sumForm : sum.node.form = .binary leftCall.node.id .add leftValue.node.id
  rightArgument : Read function.typedBody argument .word
  rightFunction : Read function.typedBody callable functionType
  rightCall : Call function.typedBody rightFunction.node.id rightArgument.node.id
  rightValue : Read function.typedBody argument .word
  difference : TypedNode function.typedBody .word
  differenceForm : difference.node.form = .binary rightCall.node.id .subtract rightValue.node.id
  expression : TypedNode function.typedBody .word
  expressionForm : expression.node.form = .conditional negation.node.id sum.node.id difference.node.id
  statement : StatementNode
  callableScheme : callable.scheme = .mono functionType
  callableRequirements : callable.schemeRequirements = []
  callableOrdinary : callable.comptime = false
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  flagCallable : flag.id ≠ callable.id
  argumentCallable : argument.id ≠ callable.id
  argumentFlag : argument.id ≠ flag.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [functionType, .bool, .word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [callable, flag, argument]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some expression.node.id)
  statementType : statement.type = .word

def IdentityShape.nodeList {function signature} (shape : IdentityShape function signature) : List Node :=
  [.expression shape.read.node, .statement shape.statement]
def SelectShape.nodeList {function signature} (shape : SelectShape function signature) : List Node :=
  [.expression shape.flagRead.node, .expression shape.negation.node,
   .expression shape.leftArgument.node, .expression shape.leftFunction.node,
   .expression shape.leftCall.node, .expression shape.leftValue.node, .expression shape.sum.node,
   .expression shape.rightArgument.node, .expression shape.rightFunction.node,
   .expression shape.rightCall.node, .expression shape.rightValue.node, .expression shape.difference.node,
   .expression shape.expression.node, .statement shape.statement]

private theorem roots_injective {left right : List StatementId}
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

theorem IdentityShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : IdentityShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := roots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
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
    have read := shape.read.typed scheme shape.binderRequirements ⟨binders, .builtin .word⟩
      head.local_self head.local_scheme_requirements_self
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm read shape.statementType)⟩

theorem SelectShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : SelectShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := roots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons callableScheme callableExtended tail =>
    cases tail with
    | cons flagScheme flagExtended tail =>
      cases tail with
      | cons argumentScheme argumentExtended tail =>
        cases tail
        have binders : TypeParameterBindersWellFormed lexical := by
          rw [TypeParameterBindersWellFormed, argumentExtended.context_fields.2.2.1,
            flagExtended.context_fields.2.2.1, callableExtended.context_fields.2.2.1]
          simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
            Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
        have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
        have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
        have callable : TypeAdmissible lexical functionType := ⟨binders, .function (.builtin .word) (.builtin .word)⟩
        have valueRead := fun (read : Read function.typedBody shape.argument .word) =>
          read.typed argumentScheme shape.argumentRequirements word
            argumentExtended.local_self argumentExtended.local_scheme_requirements_self
        have callableRead := fun (read : Read function.typedBody shape.callable functionType) =>
          read.typed callableScheme shape.callableRequirements callable
            (by cases argumentExtended; cases flagExtended
                exact .tail shape.argumentCallable (.tail shape.flagCallable callableExtended.local_self))
            (by cases argumentExtended; cases flagExtended
                exact .tail shape.argumentCallable (.tail shape.flagCallable callableExtended.local_scheme_requirements_self))
        have flagRead := shape.flagRead.typed flagScheme shape.flagRequirements bool
          (by cases argumentExtended; exact .tail shape.argumentFlag flagExtended.local_self)
          (by cases argumentExtended; exact .tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
        have negation := shape.negation.ordinary bool (shape.negationForm ▸ .unary flagRead .logicalNot)
        have leftCall := shape.leftCall.typed word (callableRead shape.leftFunction) (valueRead shape.leftArgument)
        have rightCall := shape.rightCall.typed word (callableRead shape.rightFunction) (valueRead shape.rightArgument)
        have sum := shape.sum.ordinary word
          (shape.sumForm ▸ .binary leftCall (valueRead shape.leftValue) (.wordArithmetic .add))
        have difference := shape.difference.ordinary word
          (shape.differenceForm ▸ .binary rightCall (valueRead shape.rightValue) (.wordArithmetic .subtract))
        have expression := shape.expression.ordinary word
          (shape.expressionForm ▸ .conditional negation sum difference)
        exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
          shape.statementForm expression shape.statementType)⟩

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeNode (source : TypedSource) (node : ExpressionNode) (expected : TypeSystem.Ty) : IO (TypedNode source expected) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "node lookup"
  let ⟨raw⟩ ← observed (node.rawType = expected) "node raw type"
  let ⟨type⟩ ← observed (node.type = expected) "node type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "node requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "node coercions"
  return { node, found, raw, type, requirements, coercions }

def observeCall (source : TypedSource) (callee argument : ExpressionId) (node : ExpressionNode) : IO (Call source callee argument) := do
  let typed ← observeNode source node .word
  let .call _ _ (.indirect metadata) := typed.node.form | throw (IO.userError "indirect call expected")
  let ⟨form⟩ ← observed (typed.node.form = .call callee [argument] (.indirect metadata)) "indirect call form"
  let ⟨application⟩ ← observed (metadata = ⟨1, .word, .word, []⟩) "indirect call original metadata"
  return { toTypedNode := typed, metadata, form, application }

def observeIdentity (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (IdentityShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity inputs")
  let [.expression readNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "identity nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "identity binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "identity binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "identity binderOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "identity parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "identity inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "identity returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "identity inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "identity roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "identity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "identity statementType"
  return { binder, read, statement, binderScheme, binderRequirements, binderOrdinary, parameters, inputTypes, returns, inputs, roots, statementFound, statementForm, statementType }

def observeSelect (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (SelectShape function signature) := do
  let [callable, flag, argument] := function.typedBody.inputs | throw (IO.userError "select inputs")
  let [.expression flagNode, .expression negationNode, .expression leftArgumentNode,
      .expression leftFunctionNode, .expression leftCallNode, .expression leftValueNode,
      .expression sumNode, .expression rightArgumentNode, .expression rightFunctionNode,
      .expression rightCallNode, .expression rightValueNode, .expression differenceNode,
      .expression expressionNode, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "select nodes")
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag flagNode .bool
  let negation ← observeNode function.typedBody negationNode .bool
  let leftArgument ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument leftArgumentNode .word
  let leftFunction ← Tests.SourceCoreNamedBranch.observeRead function.typedBody callable leftFunctionNode functionType
  let leftCall ← observeCall function.typedBody leftFunction.node.id leftArgument.node.id leftCallNode
  let leftValue ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument leftValueNode .word
  let sum ← observeNode function.typedBody sumNode .word
  let rightArgument ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument rightArgumentNode .word
  let rightFunction ← Tests.SourceCoreNamedBranch.observeRead function.typedBody callable rightFunctionNode functionType
  let rightCall ← observeCall function.typedBody rightFunction.node.id rightArgument.node.id rightCallNode
  let rightValue ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument rightValueNode .word
  let difference ← observeNode function.typedBody differenceNode .word
  let expression ← observeNode function.typedBody expressionNode .word
  let ⟨negationForm⟩ ← observed (negation.node.form = .unary .logicalNot flagRead.node.id) "select negationForm"
  let ⟨sumForm⟩ ← observed (sum.node.form = .binary leftCall.node.id .add leftValue.node.id) "select sumForm"
  let ⟨differenceForm⟩ ← observed (difference.node.form = .binary rightCall.node.id .subtract rightValue.node.id) "select differenceForm"
  let ⟨expressionForm⟩ ← observed (expression.node.form = .conditional negation.node.id sum.node.id difference.node.id) "select expressionForm"
  let ⟨callableScheme⟩ ← observed (callable.scheme = .mono functionType) "select callableScheme"
  let ⟨callableRequirements⟩ ← observed (callable.schemeRequirements = []) "select callableRequirements"
  let ⟨callableOrdinary⟩ ← observed (callable.comptime = false) "select callableOrdinary"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "select flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "select flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "select flagOrdinary"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "select argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "select argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "select argumentOrdinary"
  let ⟨flagCallable⟩ ← observed (flag.id ≠ callable.id) "select flagCallable"
  let ⟨argumentCallable⟩ ← observed (argument.id ≠ callable.id) "select argumentCallable"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "select argumentFlag"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "select parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [functionType, .bool, .word]) "select inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "select returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [callable, flag, argument]) "select inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "select roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "select statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some expression.node.id)) "select statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "select statementType"
  return { callable, flag, argument, flagRead, negation, negationForm, leftArgument, leftFunction, leftCall, leftValue, sum, sumForm, rightArgument, rightFunction, rightCall, rightValue, difference, differenceForm, expression, expressionForm, statement, callableScheme, callableRequirements, callableOrdinary, flagScheme, flagRequirements, flagOrdinary, argumentScheme, argumentRequirements, argumentOrdinary, flagCallable, argumentCallable, argumentFlag, parameters, inputTypes, returns, inputs, roots, statementFound, statementForm, statementType }

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function select(f: function(Word) returns (Word), flag: Bool, value: Word) returns (Word) { return !flag ? f(value) + value : f(value) - value; }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  selectFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  selectSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, selectFunction]
  signatures : program.signatures.functions = [identitySignature, selectSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  selectDeclaration : selectFunction.declaration = selectSignature.id
  distinct : identitySignature.id ≠ selectSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  selectShape : SelectShape selectFunction selectSignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  selectNodes : selectFunction.typedBody.nodes = selectShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, selectFunction], [identitySignature, selectSignature] =>
      let identityShape ← observeIdentity identityFunction identitySignature
      let selectShape ← observeSelect selectFunction selectSignature
      let ⟨methods⟩ ← observed (program.methods = []) "unexpected methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨selectDeclaration⟩ ← observed (selectFunction.declaration = selectSignature.id) "select declaration"
      let ⟨distinct⟩ ← observed (identitySignature.id ≠ selectSignature.id) "distinct declarations"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity complete source"
      let ⟨selectNodes⟩ ← observed (selectFunction.typedBody.nodes = selectShape.nodeList) "select complete source"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
          · exact identityShape.statementTyping program.signatures
          · exact False.elim (distinct (identityDeclaration.symm.trans identity))
          · exact False.elim (distinct (identity.symm.trans selectDeclaration))
          · exact selectShape.statementTyping program.signatures
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
        identityFunction, selectFunction, identitySignature, selectSignature, functions, signatures, methods,
        identityDeclaration, selectDeclaration, distinct, identityShape, selectShape, identityNodes, selectNodes⟩
    | _, _ => throw (IO.userError "operator call declaration count")

end Tests.SourceCoreOperatorCalls
