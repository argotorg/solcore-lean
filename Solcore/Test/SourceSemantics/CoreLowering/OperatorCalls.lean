import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories

/-!
# Operator call tests

Operators that invoke imported functions, from the compiler inventory through public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsFixture
/-! Actual two-row compiler inventory, original Header and diagnostic receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
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
    SourceCompiler.Seed.declaration checked.selectSignature.id]
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
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .word
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
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨resultType⟩ ← observed (row.function.inferredBodyType = .word) "original Word body result"
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
          ordinary := ordinary
          resultType := resultType
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
  selectRow : ObservedRow fixture fixture.selectSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 2
  distinctSlots : identityRow.index ≠ selectRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  selectShape : SelectShape selectRow.row.function fixture.selectSignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  selectNodes : selectRow.row.function.typedBody.nodes = selectShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let selectRow ← observeRow fixture fixture.selectSignature
  let identityShape ← observeIdentity identityRow.row.function fixture.identitySignature
  let selectShape ← observeSelect selectRow.row.function fixture.selectSignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 2) "reuse global count"
  let ⟨distinctSlots⟩ ← observed (identityRow.index ≠ selectRow.index) "reuse distinct slots"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "reuse identity nodes"
  let ⟨selectNodes⟩ ← observed (selectRow.row.function.typedBody.nodes = selectShape.nodeList) "reuse read nodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "reuse local catalog"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "reuse callable profile"
  return {
    identityRow := identityRow
    selectRow := selectRow
    globalsLength := globalsLength
    distinctSlots := distinctSlots
    identityShape := identityShape
    selectShape := selectShape
    identityNodes := identityNodes
    selectNodes := selectNodes
    noLocals := noLocals
    profile := profile }


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
    ∃ (identityInput selectInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ selectInput.row = observed.selectRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (selectPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued selectInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (selectHeader : ActualHeader fixture observed.selectRow.row),
        identityHeader.header = identityPacket.header ∧ selectHeader.header = selectPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons identityPacket (.cons selectPacket .nil))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨selectInput, selectRow, selectPacket, selectHeader, selectEq, selectSlot, selectSignature⟩ := observed.selectRow.issue
  refine ⟨identityInput, selectInput, identityRow, selectRow, identityPacket, selectPacket, identityHeader, selectHeader,
    identityEq, selectEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have selectBound := (List.getElem?_eq_some_iff.mp observed.selectRow.slot.selected).1
  rw [observed.globalsLength] at identityBound selectBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.selectRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨selectHeader.header, ?_, selectSlot.trans same.symm, ?_⟩
    · rw [selectEq]; exact .tail _ (.head _)
    · rw [same, observed.selectRow.slot.selected] at found
      exact selectSignature.trans (Option.some.inj found)


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


end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsFacts
/-! Finite original node observations supply complete metadata and identify both
real compiler rows. The two indirect calls remain in the supported expression tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

theorem ObservedProgram.identity_expressions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.identityRow.row.function.typedBody id node) :
    node = observed.identityShape.read.node := by
  have member := found.1
  rw [observed.identityNodes] at member
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.identityRow.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.identity_expressions found with same
  all_goals subst node
  · rw [observed.identityShape.read.form] at form; cases form

theorem ObservedProgram.identity_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.identityRow.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · exact observed.identityShape.read.requirements
  · intro id _tree node found
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · exact observed.identityShape.read.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments metadata form
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · rw [observed.identityShape.read.form] at form; cases form
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.select_expressions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.selectRow.row.function.typedBody id node) :
    node = observed.selectShape.flagRead.node ∨ node = observed.selectShape.negation.node ∨ node = observed.selectShape.leftArgument.node ∨ node = observed.selectShape.leftFunction.node ∨ node = observed.selectShape.leftCall.node ∨ node = observed.selectShape.leftValue.node ∨ node = observed.selectShape.sum.node ∨ node = observed.selectShape.rightArgument.node ∨ node = observed.selectShape.rightFunction.node ∨ node = observed.selectShape.rightCall.node ∨ node = observed.selectShape.rightValue.node ∨ node = observed.selectShape.difference.node ∨ node = observed.selectShape.expression.node := by
  have member := found.1
  rw [observed.selectNodes] at member
  simpa only [SelectShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedProgram.select_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.selectRow.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.select_expressions found with same | same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.selectShape.flagRead.form] at form; cases form
  · rw [observed.selectShape.negationForm] at form; cases form
  · rw [observed.selectShape.leftArgument.form] at form; cases form
  · rw [observed.selectShape.leftFunction.form] at form; cases form
  · rw [observed.selectShape.leftCall.form] at form; cases form
  · rw [observed.selectShape.leftValue.form] at form; cases form
  · rw [observed.selectShape.sumForm] at form; cases form
  · rw [observed.selectShape.rightArgument.form] at form; cases form
  · rw [observed.selectShape.rightFunction.form] at form; cases form
  · rw [observed.selectShape.rightCall.form] at form; cases form
  · rw [observed.selectShape.rightValue.form] at form; cases form
  · rw [observed.selectShape.differenceForm] at form; cases form
  · rw [observed.selectShape.expressionForm] at form; cases form

theorem ObservedProgram.select_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.selectRow.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.flagRead.requirements
    · exact observed.selectShape.negation.requirements
    · exact observed.selectShape.leftArgument.requirements
    · exact observed.selectShape.leftFunction.requirements
    · exact observed.selectShape.leftCall.requirements
    · exact observed.selectShape.leftValue.requirements
    · exact observed.selectShape.sum.requirements
    · exact observed.selectShape.rightArgument.requirements
    · exact observed.selectShape.rightFunction.requirements
    · exact observed.selectShape.rightCall.requirements
    · exact observed.selectShape.rightValue.requirements
    · exact observed.selectShape.difference.requirements
    · exact observed.selectShape.expression.requirements
  · intro id _tree node found
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.flagRead.coercions
    · exact observed.selectShape.negation.coercions
    · exact observed.selectShape.leftArgument.coercions
    · exact observed.selectShape.leftFunction.coercions
    · exact observed.selectShape.leftCall.coercions
    · exact observed.selectShape.leftValue.coercions
    · exact observed.selectShape.sum.coercions
    · exact observed.selectShape.rightArgument.coercions
    · exact observed.selectShape.rightFunction.coercions
    · exact observed.selectShape.rightCall.coercions
    · exact observed.selectShape.rightValue.coercions
    · exact observed.selectShape.difference.coercions
    · exact observed.selectShape.expression.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments metadata form
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.selectShape.flagRead.form] at form; cases form
    · rw [observed.selectShape.negationForm] at form; cases form
    · rw [observed.selectShape.leftArgument.form] at form; cases form
    · rw [observed.selectShape.leftFunction.form] at form; cases form
    · rw [observed.selectShape.leftCall.form] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.selectShape.leftCall.application]
    · rw [observed.selectShape.leftValue.form] at form; cases form
    · rw [observed.selectShape.sumForm] at form; cases form
    · rw [observed.selectShape.rightArgument.form] at form; cases form
    · rw [observed.selectShape.rightFunction.form] at form; cases form
    · rw [observed.selectShape.rightCall.form] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.selectShape.rightCall.application]
    · rw [observed.selectShape.rightValue.form] at form; cases form
    · rw [observed.selectShape.differenceForm] at form; cases form
    · rw [observed.selectShape.expressionForm] at form; cases form
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.selectRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have selectBound := (List.getElem?_eq_some_iff.mp observed.selectRow.slot.selected).1
  rw [observed.globalsLength] at identityBound selectBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.selectRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right
    have actualIndex := (observed.selectRow.prepared_slot selectHeader.prepared).2
    rw [same, ← actualIndex, selectHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) selectHeader.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.key {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row)
    (stages : ObservedStages fixture observed) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := actual.key.symm ▸ stages.descriptor

theorem ActualHeader.result_type {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row) :
    actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.identityShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.identityShape.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.select_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [functionType, .bool, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.selectShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.selectShape.callableScheme, observed.selectShape.flagScheme, observed.selectShape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm


end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsRuntime
/-! Actual unary/conditional/arithmetic expressions call an authentically issued
named handle. Both selected branches retain their original execution receipts
and consume the exact preceding returned session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def firstValue : Core.Word := Core.Word.ofNatModulo 11
def secondValue : Core.Word := Core.Word.ofNatModulo 22
def zero : Core.Word := Core.Word.ofNatModulo 0
def issuanceFuel : Nat := 1000

structure ObservedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) (value : Core.Word) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  returned : completion.value = .word value

def observePublicCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (arguments : List SourceCorePublicValues.Value) (value : Core.Word) :
    IO (ObservedCall session key arguments value) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "operator call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "operator call exhausted its execution budget")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word value then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "operator call returned an unexpected Word")

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok issued =>
    match returned : issued.val.value with
    | .function handle => pure ⟨issued.val, issued.property, handle, returned⟩
    | _ => throw (IO.userError "named issuance did not return a function")

structure ObservedInitial (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedCall session observed.identityRow.row.key [.word seed] seed

def observeInitial (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedInitial fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "named operators bootstrap exhausted")
  | .ready session =>
    let call ← observePublicCall session observed.identityRow.row.key [.word seed] seed
    return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready, call⟩

def selectArguments (handle : SourceCorePublicValues.Handle) (flag : Bool) (value : Core.Word) : List SourceCorePublicValues.Value :=
  [.function handle, .bool flag, .word value]

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  initial : ObservedInitial fixture observed
  named : ObservedNamed initial.call.completion.session observed.identityRow.row.key
  first : ObservedCall named.completion.session observed.selectRow.row.key (selectArguments named.handle false firstValue) secondValue
  next : ObservedCall first.completion.session observed.selectRow.row.key (selectArguments named.handle true secondValue) zero

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let initial ← observeInitial fixture observed
  let named ← observeNamed initial.call.completion.session observed.identityRow.row.key
  let first ← observePublicCall named.completion.session observed.selectRow.row.key (selectArguments named.handle false firstValue) secondValue
  let next ← observePublicCall first.completion.session observed.selectRow.row.key (selectArguments named.handle true secondValue) zero
  return ⟨initial, named, first, next⟩

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.identityRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedInitial.start_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedInitial fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.call.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.identityRow.row.key [.word seed]
        runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.call.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩

theorem ObservedInitial.metadata_at_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedInitial fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.identityRow.row.key [.word seed]
      runOptions.inputValidationFuel checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  have same := List.mem_singleton.mp member
  exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsSyntax
/-! The exact original recursive expression tree includes both indirect calls.
Its source occurrences and ordered argument lists come from the checker graph. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)

theorem ObservedProgram.identity_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    Syntax observed.identityRow.row.function.typedBody observed.identityShape.read.node.id :=
  .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

theorem ObservedProgram.select_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    Syntax observed.selectRow.row.function.typedBody observed.selectShape.expression.node.id := by
  apply Syntax.conditional observed.selectShape.expression.found observed.selectShape.expressionForm
  · exact .unary observed.selectShape.negation.found observed.selectShape.negationForm
      (.leaf (.read observed.selectShape.flagRead.found observed.selectShape.flagRead.form))
  · apply Syntax.binary observed.selectShape.sum.found observed.selectShape.sumForm
    · apply Syntax.call observed.selectShape.leftCall.found observed.selectShape.leftCall.form
        (.leaf (.read observed.selectShape.leftFunction.found observed.selectShape.leftFunction.form))
      intro child member
      have same := List.mem_singleton.mp member
      subst child
      exact .leaf (.read observed.selectShape.leftArgument.found observed.selectShape.leftArgument.form)
    · exact .leaf (.read observed.selectShape.leftValue.found observed.selectShape.leftValue.form)
  · apply Syntax.binary observed.selectShape.difference.found observed.selectShape.differenceForm
    · apply Syntax.call observed.selectShape.rightCall.found observed.selectShape.rightCall.form
        (.leaf (.read observed.selectShape.rightFunction.found observed.selectShape.rightFunction.form))
      intro child member
      have same := List.mem_singleton.mp member
      subst child
      exact .leaf (.read observed.selectShape.rightArgument.found observed.selectShape.rightArgument.form)
    · exact .leaf (.read observed.selectShape.rightValue.found observed.selectShape.rightValue.form)

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsSupports
/-! A complete static package is produced from the actual two issuer packets.
The Type-valued terminal dispatcher branches only on real physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

private def selectTwo {compiled : SourceCoreUnifiedCompilation.Compiled}
    {left right : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (distinct : left.slot ≠ right.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (leftValue : property left) (rightValue : property right) :
    ∀ header, header ∈ [left, right] → property header := by
  intro header member
  if sameSlot : header.slot = left.slot then
    have same : header = left := by
      rcases List.mem_cons.mp member with same | rest
      · exact same
      · have same := List.mem_singleton.mp rest
        exact False.elim (distinct (sameSlot ▸ congrArg (·.slot) same))
    exact same.symm ▸ leftValue
  else
    have same : header = right := by
      rcases List.mem_cons.mp member with same | rest
      · exact False.elim (sameSlot (congrArg (·.slot) same))
      · exact List.mem_singleton.mp rest
    exact same.symm ▸ rightValue

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  selectInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  selectRow : selectInput.row = observed.selectRow.row
  identityPacket : Issued identityInput
  selectPacket : Issued selectInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  selectHeader : ActualHeader fixture observed.selectRow.row
  identityEq : identityHeader.header = identityPacket.header
  selectEq : selectHeader.header = selectPacket.header
  rows : Inventory [identityInput, selectInput]
  rowsEq : rows = .cons identityPacket (.cons selectPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, selectInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : identityHeader.header.slot ≠ selectHeader.header.slot
  terminals : ∀ header, header ∈ headers rows → Body header
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
  selectDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named selectHeader.header.named.signature.key)

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (identityStages : ObservedStages fixture observed.identityRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, selectInput, identityRow, selectRow, identityPacket, selectPacket,
    identityHeader, selectHeader, identityEq, selectEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, selectInput] := .cons identityPacket (.cons selectPacket .nil)
  have headerList : headers rows = [identityHeader.header, selectHeader.header] := by
    simp only [rows, headers, identityEq, selectEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have selectIndex : selectHeader.header.slot = observed.selectRow.index :=
    selectHeader.aligned.slot.trans (observed.selectRow.prepared_slot selectHeader.prepared).2
  have slotsDistinct : identityHeader.header.slot ≠ selectHeader.header.slot := by
    rw [identityIndex, selectIndex]
    exact observed.distinctSlots
  have inputDistinct : identityInput.prepared.index ≠ selectInput.prepared.index := by
    have left : identityHeader.header.slot = identityInput.prepared.index := by
      rw [identityEq]; exact identityPacket.aligned.slot
    have right : selectHeader.header.slot = selectInput.prepared.index := by
      rw [selectEq]; exact selectPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  obtain ⟨identityTerminal, identityDiagnostic, identityExpression, identityPoint⟩ := identityHeader.terminal
    observed.identityShape.read.node.id observed.identityShape.statement observed.identityShape.roots
    observed.identityShape.statementFound observed.identityShape.statementForm
  obtain ⟨identitySupport⟩ := CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    identityTerminal identityDiagnostic receiver fixture.source_wellFormed
    (by rw [identityHeader.source]; exact observed.identity_metadata identityTerminal.prepared.named)
    (by rw [identityHeader.source, identityExpression]; exact observed.identity_syntax)
    (actualStagePrepared fixture) identityPoint
  obtain ⟨selectTerminal, selectDiagnostic, selectExpression, selectPoint⟩ := selectHeader.terminal
    observed.selectShape.expression.node.id observed.selectShape.statement observed.selectShape.roots
    observed.selectShape.statementFound observed.selectShape.statementForm
  obtain ⟨selectSupport⟩ := CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    selectTerminal selectDiagnostic receiver fixture.source_wellFormed
    (by rw [selectHeader.source]; exact observed.select_metadata selectTerminal.prepared.named)
    (by rw [selectHeader.source, selectExpression]; exact observed.select_syntax)
    (actualStagePrepared fixture) selectPoint
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo slotsDistinct property
      ⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal identityTerminal, .recursive identitySupport⟩
      ⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal selectTerminal, .recursive selectSupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    selectInput := selectInput
    identityRow := identityRow
    selectRow := selectRow
    identityPacket := identityPacket
    selectPacket := selectPacket
    identityHeader := identityHeader
    selectHeader := selectHeader
    identityEq := identityEq
    selectEq := selectEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := by
      intro mapping world function native bindings parameter result association
      cases association with
      | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
          apply False.elim
          have found := code.sourceFound
          rcases observed.cached_source identityHeader selectHeader support.caller.selected with original | original
          · rw [support.source.trans original] at found
            exact False.elim (observed.identity_no_lambda (lookupExpression?_sound found) code.sourceForm)
          · rw [support.source.trans original] at found
            exact False.elim (observed.select_no_lambda (lookupExpression?_sound found) code.sourceForm)
      | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
          exact False.elim (fixture.no_principal support.principal)
    identityDescriptor := identityHeader.descriptor identityStages
    selectDescriptor := selectHeader.descriptor selectStages }⟩

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsCommon
/-! Retained callers connect the exact sessions and Source heaps of both named calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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
    support.identityHeader.header session mapping world heap store caller entries

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
      support.identityHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsSelection
/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.identityRow.row.key ≠ observed.selectRow.row.key := by
  intro same
  have globals : observed.identityRow.global.key = observed.selectRow.global.key :=
    observed.identityRow.globalKey.trans (same.trans observed.selectRow.globalKey.symm)
  exact observed.distinctSlots (observed.identityRow.slot.unique observed.selectRow.slot globals).2

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

theorem selected_identity_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, selectHeader.header] root header)
    (key : root.key = observed.identityRow.row.key) : header = identityHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, selectHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_select_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, selectHeader.header] root header)
    (key : root.key = observed.selectRow.row.key) : header = selectHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey)
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

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (identityHeader : ActualHeader fixture observed.identityRow.row)
  (selectHeader : ActualHeader fixture observed.selectRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_identity (request : Started [identityHeader.header, selectHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.identityRow.row.key arguments fuel world store) :
    request.header = identityHeader.header :=
  selected_identity_root identityHeader selectHeader request.selected (started_key request)

theorem selected_select (request : Started [identityHeader.header, selectHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.selectRow.row.key arguments fuel world store) :
    request.header = selectHeader.header :=
  selected_select_root identityHeader selectHeader request.selected (started_key request)

theorem selected_identity_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.identityRow.row.key arguments fuel world store) : request.header = identityHeader.header := by
  subst headers
  exact selected_identity identityHeader selectHeader request

theorem selected_select_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.selectRow.row.key arguments fuel world store) : request.header = selectHeader.header := by
  subst headers
  exact selected_select identityHeader selectHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.identityHeader.header, support.selectHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.identityEq, support.selectEq]



end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsIssuance
/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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

theorem identity_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.identityPacket.header.named.specialized.function.type = .function .word .word := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.identityPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.identityPacket.header.named.specialized.function.type = _ at shape
  rw [← support.identityPacket.sourceAt.frame.result, ← support.identityEq,
    support.identityHeader.identity_types, support.identityHeader.result_type] at shape
  rw [support.identityEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

private theorem named_handle_type (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.identityRow.row.key) :
    call.handle.sourceType = .function .word .word := by
  obtain ⟨artifact, before, actual, beforeAt, issued, completedAt⟩ := call.issued
  cases indexed_artifact_eq state.atSession beforeAt
  have actualType := issued.function_source_type (completedAt.1.symm.trans call.returned)
  obtain ⟨expected, native, _same, sourceType, _fuel, _encoded, factory⟩ := issued.receipt
  have actualFactory : fixture.recipe.NamedCallableAt observed.identityRow.row.key expected native := by
    have atRecipe := state.atRecipe
    cases artifactEq : state.artifact
    rename_i authority actualRecipe
    rw [artifactEq] at atRecipe factory
    change actualRecipe = fixture.recipe at atRecipe
    cases atRecipe
    exact factory
  have keyEq : observed.identityRow.row.key = support.identityPacket.header.named.signature.key :=
    support.identityHeader.key.symm.trans (congrArg (fun header => header.named.signature.key) support.identityEq)
  rw [keyEq] at actualFactory
  obtain ⟨signature, index, specialized, location, closure, identity, descriptor,
    _global, _key, record, expectedType, _remaining⟩ := actualFactory.prepared fixture.recipePrepared
  have specializedEq := Except.ok.inj
    (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record _ support.identityPacket.header))
  subst specialized
  exact actualType.trans (sourceType.trans (expectedType.trans (identity_source_type support)))

/-- Named issuance appends the compiler-selected identity global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.identityRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function .word .word ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function .word .word ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.identityPacket.header.named.specialized support.identityInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.identityPacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.identityPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.identityEq, support.identityHeader.key]
    exact call.issued
  obtain ⟨actual, native, actualAt, retained⟩ := RecursiveNamedPublicHistoryIssuance.named_remembered
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.identityPacket member
    receiver.completion.result.context.registry state.receiving.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile state.history state.atRecipe state.atSession issued call.returned fixture.source_wellFormed
  have registry := (call.issued.same_runtime.indexed state.atSession actualAt.2.2.2).registry_at state.registry
  let entry : Entry := ⟨support.identityPacket.header.named.specialized.function.type,
    .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.identityPacket.header.named.specialized support.identityInput.prepared.available)), call.handle, native,
    Core.CallableContract.functionType support.identityPacket.header.named.signature.parameterType
      support.identityPacket.header.named.signature.resultType, issuanceFuel⟩
  refine ⟨entry, identity_source_type support, rfl, named_handle_type state call, rfl,
    ⟨state.artifact, actual.session, state.mapping, state.world, state.heap, state.store, state.caller,
      actualAt.2.2.2, state.atRecipe, state.receiving, state.issued, state.extension, registry, retained⟩, rfl⟩

end State
end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsSeed
/-! The initial nonempty-loop call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed.identityRow)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.identityHeader.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.identityHeader.header.function)
        ⟨[]⟩ [.word seed] (.value (.word seed)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.identityHeader.header := by
    apply selected_identity_root (fixture := fixture) (observed := observed)
      support.identityHeader support.selectHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.identityRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.identityHeader.header.function.context
      (support.identityHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed] [.word seed] := by
    rw [support.identityHeader.identity_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.identityHeader.header support.identityInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.identityPacket.header.named.specialized support.identityInput.prepared.available)) := by
    rw [support.identityEq]
    exact support.identityPacket.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.identityHeader.header.function)
      first.call.started first.call.executed .skip support.identityDescriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.identityHeader.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.identityHeader.output result
  let state : RetainedState support first.call.completion.session [] := {
    artifact := artifact
    session := actual.session
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
  exact ⟨state, support.identityInput.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsStep
/-! A retained actual named handle is passed through both branches of the same checked operator expression. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem RetainedState.select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : RetainedState support session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = functionType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {value returned : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) returned)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support support.selectHeader.header invocation state.heap
        [entry.source, .bool flag, .word value] (.value (.word returned)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.selectHeader.header :=
    selected_select_at support.identityHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      (selectArguments handle flag value) [entry.source, .bool flag, .word value] := by
    rw [selectedHeader, support.selectHeader.select_input_types]
    change RecursiveNamedPublicFunctionHistoryInputs.Inputs entries support.selectHeader.header.function.context
      [functionType, .bool, .word] [.function handle, .bool flag, .word value]
      [entry.source, .bool flag, .word value]
    refine .cons ?_ (.cons (.data ?_ ?_) (.cons (.data ?_ ?_) .nil))
    · rw [← entryType, ← entryHandle]; exact .retained entry member
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
  obtain ⟨receiving, _receiverMember, contextAt, issued, extended, retained, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history state.registry request.started
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.selectDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued issued present (state.extension.trans extended) represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := receiving)
      (receiver := issued) (profile := observed.profile) (observations := support.observations)
      (extension := receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := retained)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.selectHeader.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.selectHeader.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [← contextAt] at returnedRegistry
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (entries : List Entry) {handle : SourceCorePublicValues.Handle} {flag : Bool} {value result : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) result)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word result ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : RetainedState support session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = functionType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {value returned : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) returned)
    (ready : session.ExportsReady) {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [entry.source, .bool flag, .word value] (.value (.word returned)) after) :
    ForwardAt support entries call after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.selectHeader.header :=
    selected_select_at support.identityHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      (selectArguments handle flag value) [entry.source, .bool flag, .word value] := by
    rw [selectedHeader, support.selectHeader.select_input_types]
    change RecursiveNamedPublicFunctionHistoryInputs.Inputs entries support.selectHeader.header.function.context
      [functionType, .bool, .word] [.function handle, .bool flag, .word value]
      [entry.source, .bool flag, .word value]
    refine .cons ?_ (.cons (.data ?_ ?_) (.cons (.data ?_ ?_) .nil))
    · rw [← entryType, ← entryHandle]; exact .retained entry member
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
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
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
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
  rw [resultType, selectedHeader, support.selectHeader.result_type] at requested
  have nativeWord : payload = .word returned := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.selectHeader.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
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
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreOperatorCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreOperatorCallsPublicExecution
/-! The actual compiler emits a conditional containing two indirect calls and
Word arithmetic. The same genuinely issued identity handle is reused in both
selected branches, on the exact sessions returned by the previous executions.
Independent Source traces entail sufficient public fuel for both calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (identityStages : ObservedStages fixture observed.identityRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (initial : RetainedState support sequence.initial.call.completion.session [])
      (entry : Entry) (issued : RetainedState support sequence.named.completion.session [entry])
      (first : RetainedState support sequence.first.completion.session [entry])
      (second : RetainedState support sequence.next.completion.session [entry]),
      entry.sourceType = functionType ∧ entry.handle = sequence.named.handle ∧
      issued.heap = initial.heap ∧
      SourceCall support support.identityHeader.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function)
        ⟨[]⟩ [.word seed] (.value (.word seed)) initial.heap ∧
      SourceCall support support.selectHeader.header
        (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
        issued.heap [entry.source, .bool false, .word firstValue] (.value (.word secondValue)) first.heap ∧
      SourceCall support support.selectHeader.header
        (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
        first.heap [entry.source, .bool true, .word secondValue] (.value (.word zero)) second.heap ∧
      ForwardAt support [entry] sequence.first first.heap ∧
      ForwardAt support [entry] sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed identityStages selectStages
    receiver.completion.result.context.registry receiver.issued
  obtain ⟨initial, initialTrace⟩ := first_meaning support identityStages sequence.initial
  obtain ⟨entry, entryType, entryHandle, _handleType, _source, issued, sameHeap⟩ :=
    remember_named initial sequence.named
  have member : entry ∈ [entry] := .head _
  obtain ⟨first, firstTrace⟩ := issued.select entry member entryType entryHandle sequence.first
    (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
  obtain ⟨second, secondTrace⟩ := first.select entry member entryType entryHandle sequence.next
    (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have seededReady := sequence.initial.call.executed.exportsReady initialReady
  have issuedReady := sequence.named.issued.exportsReady seededReady
  have firstReady := sequence.first.executed.exportsReady issuedReady
  exact ⟨receiver, support, initial, entry, issued, first, second, entryType, entryHandle,
    sameHeap, initialTrace, firstTrace, secondTrace,
    forward_select issued entry member entryType entryHandle sequence.first issuedReady firstTrace,
    forward_select first entry member entryType entryHandle sequence.next firstReady secondTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let identityStages ← observeStages fixture observed.identityRow
  let selectStages ← observeStages fixture observed.selectRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed identityStages selectStages sequence
  IO.println "Actual indirect identity calls under unary/conditional/Word operators: false11→22 then true22→0; same handle, exact Source histories, sufficient public fuel"

end Tests.SourceCoreOperatorCalls
end
