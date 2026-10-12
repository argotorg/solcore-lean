import Solcore.Test.SourceCoreDirectCallsSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics
abbrev FactoryShape := Tests.SourceCoreDirectCalls.FactoryShape
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev closureType : TypeSystem.Ty := .function .unit .word
abbrev containerType : TypeSystem.Ty := .mapping .word closureType
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

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]

/-- Exact original metadata of a monomorphic direct call. -/
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (parameter expected : TypeSystem.Ty) where
  callee : TypedNode source (.function parameter expected)
  value : TypedNode source expected
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[], [], .function parameter expected⟩
  inputs : signature.parameterTypes = [parameter]
  returns : signature.returnTypes = [expected]
  exact : instantiation = ⟨signature.id, [], .function parameter expected, [],
    signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {parameter expected : TypeSystem.Ty}
    (call : DirectCall source signature argument parameter expected) {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions)
    (admissible : TypeAdmissible context expected)
    (argumentTyped : ExpressionHasType source context argument parameter) :
    ExpressionHasType source context call.value.node.id expected := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · simpa only [call.scheme] using ParameterSubstitution.exact_empty
    · intro parameter replacement contained; cases contained
    · simp [call.scheme, parameter_nil]
    · simp [call.scheme]
  have application : DeclarationApplicationValid context call.instantiation [parameter] expected [] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, parameter_nil]
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

structure IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) (expected : TypeSystem.Ty) where
  binder : TypedBinder
  read : Read function.typedBody binder expected
  statement : StatementNode
  binderScheme : binder.scheme = .mono expected
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [expected]
  returns : signature.returnTypes = [expected]
  inputs : function.typedBody.inputs = [binder]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = expected

theorem IdentityShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature} {expected : TypeSystem.Ty}
    (shape : IdentityShape function signature expected) (signatures : ProgramSignatures)
    (admissible : ∀ context, TypeParameterBindersWellFormed context → TypeAdmissible context expected) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := expected, hasValue := true, sawReturn := true, control := .returned}
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
    have read := shape.read.typed scheme shape.binderRequirements (admissible lexical binders)
      head.local_self head.local_scheme_requirements_self
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm read shape.statementType)⟩

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (argument : ExpressionId) (callee value : ExpressionNode) (parameter expected : TypeSystem.Ty) :
    IO (DirectCall source signature argument parameter expected) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function parameter expected)
  let value ← Tests.SourceCoreOperatorCalls.observeNode source value expected
  let .reference name (.declaration instantiation) := callee.node.form
    | throw (IO.userError "direct synthetic declaration callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "direct callee"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.declaration instantiation)) "direct call"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[], [], .function parameter expected⟩) "direct signature"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [parameter]) "direct parameter"
  let ⟨returns⟩ ← observed (signature.returnTypes = [expected]) "direct return"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [], .function parameter expected, [],
    signature.parameterComptime, signature.returnComptime⟩) "direct exact metadata"
  return {callee, value, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}

def observeIdentity (function : CheckedFunction) (signature : ProgramFunctionSignature) (expected : TypeSystem.Ty) : IO (IdentityShape function signature expected) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity inputs")
  let [.expression readNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "identity nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode expected
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono expected) "identity binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "identity binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "identity binderOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "identity parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [expected]) "identity inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [expected]) "identity returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "identity inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "identity roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "identity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = expected) "identity statementType"
  return { binder, read, statement, binderScheme, binderRequirements, binderOrdinary, parameters, inputTypes, returns, inputs, roots, statementFound, statementForm, statementType }


structure SelectShape (function : CheckedFunction) (signature echo choose : ProgramFunctionSignature) where
  table : TypedBinder
  key : TypedBinder
  tableRead : Read function.typedBody table containerType
  keyRead : Read function.typedBody key .word
  base : DirectCall function.typedBody echo tableRead.node.id containerType containerType
  lookup : DirectCall function.typedBody choose keyRead.node.id .word .word
  value : TypedNode function.typedBody closureType
  form : value.node.form = .index base.value.node.id lookup.value.node.id
  statement : StatementNode
  tableScheme : table.scheme = .mono containerType
  tableRequirements : table.schemeRequirements = []
  tableOrdinary : table.comptime = false
  keyScheme : key.scheme = .mono .word
  keyRequirements : key.schemeRequirements = []
  keyOrdinary : key.comptime = false
  keyTable : key.id ≠ table.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [containerType, .word]
  returns : signature.returnTypes = [closureType]
  inputs : function.typedBody.inputs = [table, key]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some value.node.id)
  statementType : statement.type = closureType

def IdentityShape.nodeList {function signature expected} (shape : IdentityShape function signature expected) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

def SelectShape.nodeList {function signature echo choose} (shape : SelectShape function signature echo choose) : List Node :=
  [.expression shape.tableRead.node, .expression shape.base.callee.node, .expression shape.base.value.node,
   .expression shape.keyRead.node, .expression shape.lookup.callee.node, .expression shape.lookup.value.node,
   .expression shape.value.node, .statement shape.statement]

theorem SelectShape.statementTyping {function signature echo choose}
    (shape : SelectShape function signature echo choose) (signatures : ProgramSignatures)
    (echoMember : echo ∈ signatures.functions) (chooseMember : choose ∈ signatures.functions) :
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
  | cons tableScheme tableHead tail =>
    cases tail with
    | cons keyScheme keyHead tail =>
      cases tail
      have binders : TypeParameterBindersWellFormed lexical := by
        rw [TypeParameterBindersWellFormed, keyHead.context_fields.2.2.1, tableHead.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
      have fields : lexical.signatures = signatures := by
        rw [keyHead.context_fields.1, tableHead.context_fields.1]
        rfl
      have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
      have callable : TypeAdmissible lexical closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
      have container : TypeAdmissible lexical containerType := ⟨binders, .mapping (.builtin .word) (.function (.builtin .unit) (.builtin .word))⟩
      have tableTyped := shape.tableRead.typed shape.tableScheme shape.tableRequirements container
        (by cases keyHead; exact .tail shape.keyTable tableHead.local_self)
        (by cases keyHead; exact .tail shape.keyTable tableHead.local_scheme_requirements_self)
      have keyTyped := shape.keyRead.typed shape.keyScheme shape.keyRequirements word
        keyHead.local_self keyHead.local_scheme_requirements_self
      have baseTyped := shape.base.typed (fields ▸ echoMember) container tableTyped
      have lookupTyped := shape.lookup.typed (fields ▸ chooseMember) word keyTyped
      have indexTyped := shape.value.ordinary callable (shape.form ▸ ExpressionFormHasRawType.index baseTyped lookupTyped)
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm indexTyped shape.statementType)⟩

def observeSelect (function : CheckedFunction) (signature echo choose : ProgramFunctionSignature) :
    IO (SelectShape function signature echo choose) := do
  let [table, key] := function.typedBody.inputs | throw (IO.userError "select inputs")
  let [Node.expression tableNode, Node.expression baseCallee, Node.expression baseNode,
       Node.expression keyNode, Node.expression lookupCallee, Node.expression lookupNode,
       Node.expression valueNode, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "select occurrences")
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody table tableNode containerType
  let keyRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody key keyNode .word
  let base ← observeDirect function.typedBody echo tableRead.node.id baseCallee baseNode containerType containerType
  let lookup ← observeDirect function.typedBody choose keyRead.node.id lookupCallee lookupNode .word .word
  let value ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody valueNode closureType
  let ⟨form⟩ ← observed (value.node.form = .index base.value.node.id lookup.value.node.id) "select form"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono containerType) "select tableScheme"
  let ⟨tableRequirements⟩ ← observed (table.schemeRequirements = []) "select tableRequirements"
  let ⟨tableOrdinary⟩ ← observed (table.comptime = false) "select tableOrdinary"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "select keyScheme"
  let ⟨keyRequirements⟩ ← observed (key.schemeRequirements = []) "select keyRequirements"
  let ⟨keyOrdinary⟩ ← observed (key.comptime = false) "select keyOrdinary"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "select keyTable"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "select parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [containerType, .word]) "select inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType]) "select returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [table, key]) "select inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "select roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "select statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some value.node.id)) "select statementForm"
  let ⟨statementType⟩ ← observed (statement.type = closureType) "select statementType"
  return {table, key, tableRead, keyRead, base, lookup, value, statement, form, tableScheme, tableRequirements, tableOrdinary, keyScheme, keyRequirements, keyOrdinary, keyTable, parameters, inputTypes, returns, inputs, roots, statementFound, statementForm, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content := "function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function echo(table: mapping(Word => function() returns (Word))) returns (mapping(Word => function() returns (Word))) { return table; } function choose(key: Word) returns (Word) { return key; } function select(table: mapping(Word => function() returns (Word)), key: Word) returns (function() returns (Word)) { return echo(table)[choose(key)]; }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  echoFunction : CheckedFunction
  echoSignature : ProgramFunctionSignature
  chooseFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  selectFunction : CheckedFunction
  selectSignature : ProgramFunctionSignature
  functions : program.functions = [makeFunction, echoFunction, chooseFunction, selectFunction]
  signatures : program.signatures.functions = [makeSignature, echoSignature, chooseSignature, selectSignature]
  methods : program.methods = []
  makeDeclaration : makeFunction.declaration = makeSignature.id
  echoDeclaration : echoFunction.declaration = echoSignature.id
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  selectDeclaration : selectFunction.declaration = selectSignature.id
  makeEcho : makeSignature.id ≠ echoSignature.id
  makeChoose : makeSignature.id ≠ chooseSignature.id
  makeSelect : makeSignature.id ≠ selectSignature.id
  echoChoose : echoSignature.id ≠ chooseSignature.id
  echoSelect : echoSignature.id ≠ selectSignature.id
  chooseSelect : chooseSignature.id ≠ selectSignature.id
  makeShape : FactoryShape makeFunction makeSignature
  echoShape : IdentityShape echoFunction echoSignature containerType
  chooseShape : IdentityShape chooseFunction chooseSignature .word
  selectShape : SelectShape selectFunction selectSignature echoSignature chooseSignature
  makeNodes : makeFunction.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  echoNodes : echoFunction.typedBody.nodes = echoShape.nodeList
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  selectNodes : selectFunction.typedBody.nodes = selectShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [makeFunction, echoFunction, chooseFunction, selectFunction], [makeSignature, echoSignature, chooseSignature, selectSignature] =>
      let makeShape ← Tests.SourceCoreDirectCalls.shape makeFunction makeSignature
      let echoShape ← observeIdentity echoFunction echoSignature containerType
      let chooseShape ← observeIdentity chooseFunction chooseSignature .word
      let selectShape ← observeSelect selectFunction selectSignature echoSignature chooseSignature
      let ⟨methods⟩ ← observed (program.methods = []) "index methods"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨echoDeclaration⟩ ← observed (echoFunction.declaration = echoSignature.id) "echo declaration"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "choose declaration"
      let ⟨selectDeclaration⟩ ← observed (selectFunction.declaration = selectSignature.id) "select declaration"
      let ⟨makeEcho⟩ ← observed (makeSignature.id ≠ echoSignature.id) "index makeEcho"
      let ⟨makeChoose⟩ ← observed (makeSignature.id ≠ chooseSignature.id) "index makeChoose"
      let ⟨makeSelect⟩ ← observed (makeSignature.id ≠ selectSignature.id) "index makeSelect"
      let ⟨echoChoose⟩ ← observed (echoSignature.id ≠ chooseSignature.id) "index echoChoose"
      let ⟨echoSelect⟩ ← observed (echoSignature.id ≠ selectSignature.id) "index echoSelect"
      let ⟨chooseSelect⟩ ← observed (chooseSignature.id ≠ selectSignature.id) "index chooseSelect"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "index make nodes"
      let ⟨echoNodes⟩ ← observed (echoFunction.typedBody.nodes = echoShape.nodeList) "index echo nodes"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "index choose nodes"
      let ⟨selectNodes⟩ ← observed (selectFunction.typedBody.nodes = selectShape.nodeList) "index select nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl | rfl
          · exact makeShape.statementTyping program.signatures
          · exact False.elim (makeEcho (makeDeclaration.symm.trans identity))
          · exact False.elim (makeChoose (makeDeclaration.symm.trans identity))
          · exact False.elim (makeSelect (makeDeclaration.symm.trans identity))
          · exact False.elim (makeEcho (identity.symm.trans echoDeclaration))
          · exact echoShape.statementTyping program.signatures (fun _ binders => ⟨binders, .mapping (.builtin .word) (.function (.builtin .unit) (.builtin .word))⟩)
          · exact False.elim (echoChoose (echoDeclaration.symm.trans identity))
          · exact False.elim (echoSelect (echoDeclaration.symm.trans identity))
          · exact False.elim (makeChoose (identity.symm.trans chooseDeclaration))
          · exact False.elim (echoChoose (identity.symm.trans chooseDeclaration))
          · exact chooseShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (chooseSelect (chooseDeclaration.symm.trans identity))
          · exact False.elim (makeSelect (identity.symm.trans selectDeclaration))
          · exact False.elim (echoSelect (identity.symm.trans selectDeclaration))
          · exact False.elim (chooseSelect (identity.symm.trans selectDeclaration))
          · exact selectShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        makeFunction, echoFunction, chooseFunction, selectFunction, makeSignature, echoSignature, chooseSignature, selectSignature, functions, signatures, methods, makeDeclaration, echoDeclaration, chooseDeclaration, selectDeclaration, makeEcho, makeChoose, makeSelect, echoChoose, echoSelect, chooseSelect, makeShape, echoShape, chooseShape, selectShape, makeNodes, echoNodes, chooseNodes, selectNodes }
    | _, _ => throw (IO.userError "index declaration count")

end Tests.SourceCoreRecursiveIndex
