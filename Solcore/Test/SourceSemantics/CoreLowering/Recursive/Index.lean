import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.PublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions

/-!
# Recursive index tests

Recursive indexing of mappings through one compiler profile and public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
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
  let seeds := [SourceCompiler.Seed.declaration checked.makeSignature.id,
    SourceCompiler.Seed.declaration checked.echoSignature.id,
    SourceCompiler.Seed.declaration checked.chooseSignature.id,
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
  makeRow : ObservedRow fixture fixture.makeSignature
  echoRow : ObservedRow fixture fixture.echoSignature
  chooseRow : ObservedRow fixture fixture.chooseSignature
  selectRow : ObservedRow fixture fixture.selectSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 4
  makeEcho : makeRow.index ≠ echoRow.index
  makeChoose : makeRow.index ≠ chooseRow.index
  makeSelect : makeRow.index ≠ selectRow.index
  echoChoose : echoRow.index ≠ chooseRow.index
  echoSelect : echoRow.index ≠ selectRow.index
  chooseSelect : chooseRow.index ≠ selectRow.index
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature
  echoShape : IdentityShape echoRow.row.function fixture.echoSignature containerType
  chooseShape : IdentityShape chooseRow.row.function fixture.chooseSignature .word
  selectShape : SelectShape selectRow.row.function fixture.selectSignature fixture.echoSignature fixture.chooseSignature
  makeNodes : makeRow.row.function.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  echoNodes : echoRow.row.function.typedBody.nodes = echoShape.nodeList
  chooseNodes : chooseRow.row.function.typedBody.nodes = chooseShape.nodeList
  selectNodes : selectRow.row.function.typedBody.nodes = selectShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let makeRow ← observeRow fixture fixture.makeSignature
  let echoRow ← observeRow fixture fixture.echoSignature
  let chooseRow ← observeRow fixture fixture.chooseSignature
  let selectRow ← observeRow fixture fixture.selectSignature
  let makeShape ← Tests.SourceCoreDirectCalls.shape makeRow.row.function fixture.makeSignature
  let echoShape ← observeIdentity echoRow.row.function fixture.echoSignature containerType
  let chooseShape ← observeIdentity chooseRow.row.function fixture.chooseSignature .word
  let selectShape ← observeSelect selectRow.row.function fixture.selectSignature fixture.echoSignature fixture.chooseSignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 4) "index compiled globalsLength"
  let ⟨makeEcho⟩ ← observed (makeRow.index ≠ echoRow.index) "index compiled makeEcho"
  let ⟨makeChoose⟩ ← observed (makeRow.index ≠ chooseRow.index) "index compiled makeChoose"
  let ⟨makeSelect⟩ ← observed (makeRow.index ≠ selectRow.index) "index compiled makeSelect"
  let ⟨echoChoose⟩ ← observed (echoRow.index ≠ chooseRow.index) "index compiled echoChoose"
  let ⟨echoSelect⟩ ← observed (echoRow.index ≠ selectRow.index) "index compiled echoSelect"
  let ⟨chooseSelect⟩ ← observed (chooseRow.index ≠ selectRow.index) "index compiled chooseSelect"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = [.expression makeShape.read, .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "index compiled make nodes"
  let ⟨echoNodes⟩ ← observed (echoRow.row.function.typedBody.nodes = echoShape.nodeList) "index compiled echo nodes"
  let ⟨chooseNodes⟩ ← observed (chooseRow.row.function.typedBody.nodes = chooseShape.nodeList) "index compiled choose nodes"
  let ⟨selectNodes⟩ ← observed (selectRow.row.function.typedBody.nodes = selectShape.nodeList) "index compiled select nodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "index noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "index profile"
  return {makeRow, echoRow, chooseRow, selectRow, makeShape, echoShape, chooseShape, selectShape, globalsLength, makeEcho, makeChoose, makeSelect, echoChoose, echoSelect, chooseSelect, makeNodes, echoNodes, chooseNodes, selectNodes, noLocals, profile}

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

/-- The four authentic headers cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (makeInput echoInput chooseInput selectInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      makeInput.row = observed.makeRow.row ∧ echoInput.row = observed.echoRow.row ∧ chooseInput.row = observed.chooseRow.row ∧ selectInput.row = observed.selectRow.row ∧
      ∃ (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (echoPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued echoInput)
        (choosePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseInput)
        (selectPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued selectInput),
      ∃ (makeHeader : ActualHeader fixture observed.makeRow.row)
        (echoHeader : ActualHeader fixture observed.echoRow.row)
        (chooseHeader : ActualHeader fixture observed.chooseRow.row)
        (selectHeader : ActualHeader fixture observed.selectRow.row),
        makeHeader.header = makePacket.header ∧ echoHeader.header = echoPacket.header ∧ chooseHeader.header = choosePacket.header ∧ selectHeader.header = selectPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket .nil))))) := by
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨echoInput, echoRow, echoPacket, echoHeader, echoEq, echoSlot, echoSignature⟩ := observed.echoRow.issue
  obtain ⟨chooseInput, chooseRow, choosePacket, chooseHeader, chooseEq, chooseSlot, chooseSignature⟩ := observed.chooseRow.issue
  obtain ⟨selectInput, selectRow, selectPacket, selectHeader, selectEq, selectSlot, selectSignature⟩ := observed.selectRow.issue
  refine ⟨makeInput, echoInput, chooseInput, selectInput, makeRow, echoRow, chooseRow, selectRow, makePacket, echoPacket, choosePacket, selectPacket, makeHeader, echoHeader, chooseHeader, selectHeader, makeEq, echoEq, chooseEq, selectEq, ?_⟩
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have echoBound := (List.getElem?_eq_some_iff.mp observed.echoRow.slot.selected).1
  have chooseBound := (List.getElem?_eq_some_iff.mp observed.chooseRow.slot.selected).1
  have selectBound := (List.getElem?_eq_some_iff.mp observed.selectRow.slot.selected).1
  rw [observed.globalsLength] at makeBound echoBound chooseBound selectBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.echoRow.index ∨ index = observed.chooseRow.index ∨ index = observed.selectRow.index := by
    have makeEcho := observed.makeEcho
    have makeChoose := observed.makeChoose
    have makeSelect := observed.makeSelect
    have echoChoose := observed.echoChoose
    have echoSelect := observed.echoSelect
    have chooseSelect := observed.chooseSelect
    omega
  rcases casesIndex with same | same | same | same
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .head _
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨echoHeader.header, ?_, echoSlot.trans same.symm, ?_⟩
    · rw [echoEq]; exact .tail _ (.head _)
    · rw [same, observed.echoRow.slot.selected] at found
      exact echoSignature.trans (Option.some.inj found)
  · refine ⟨chooseHeader.header, ?_, chooseSlot.trans same.symm, ?_⟩
    · rw [chooseEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.chooseRow.slot.selected] at found
      exact chooseSignature.trans (Option.some.inj found)
  · refine ⟨selectHeader.header, ?_, selectSlot.trans same.symm, ?_⟩
    · rw [selectEq]; exact .tail _ (.tail _ (.tail _ (.head _)))
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

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexLeafSupport
/-! The actual echo and choose rows are compiler-produced read bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem echo_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.echoRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.echoShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.echoNodes] at present
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.echo_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [echo_expression observed found]
    exact observed.echoShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [echo_expression observed found]
    exact observed.echoShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [echo_expression observed found, observed.echoShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.echo_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.echoShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.echoShape.read.found observed.echoShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.echo_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.echoShape.read.node.id)
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
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.echo_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.echo_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.echo_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.echoShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.echoShape.read.node.id
    observed.echoShape.statement observed.echoShape.roots observed.echoShape.statementFound observed.echoShape.statementForm
  exact ⟨terminal, expression, ActualHeader.echo_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

private theorem choose_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.chooseRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.chooseShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.chooseNodes] at present
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.choose_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [choose_expression observed found]
    exact observed.chooseShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [choose_expression observed found]
    exact observed.chooseShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [choose_expression observed found, observed.chooseShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.choose_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.chooseShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.chooseShape.read.found observed.chooseShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.choose_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.chooseShape.read.node.id)
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
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.choose_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.choose_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.choose_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.chooseShape.read.node.id
    observed.chooseShape.statement observed.chooseShape.roots observed.chooseShape.statementFound observed.chooseShape.statementForm
  exact ⟨terminal, expression, ActualHeader.choose_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexMakeSupport
/-! Concrete make support and the complete closure family for the four-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
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

theorem ObservedProgram.cached_rows {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized = observed.makeRow.row ∨ named.specialized = observed.echoRow.row ∨ named.specialized = observed.chooseRow.row ∨ named.specialized = observed.selectRow.row := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 4 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have echoBound := (List.getElem?_eq_some_iff.mp observed.echoRow.slot.selected).1
  have chooseBound := (List.getElem?_eq_some_iff.mp observed.chooseRow.slot.selected).1
  have selectBound := (List.getElem?_eq_some_iff.mp observed.selectRow.slot.selected).1
  rw [observed.globalsLength] at makeBound echoBound chooseBound selectBound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.echoRow.index ∨ index = observed.chooseRow.index ∨ index = observed.selectRow.index := by
    have makeEcho := observed.makeEcho
    have makeChoose := observed.makeChoose
    have makeSelect := observed.makeSelect
    have echoChoose := observed.echoChoose
    have echoSelect := observed.echoSelect
    have chooseSelect := observed.chooseSelect
    omega
  rcases casesIndex with same | same | same | same
  · left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact makeHeader.prepared.same
  · right; left
    have actualIndex := (observed.echoRow.prepared_slot echoHeader.prepared).2
    rw [same, ← actualIndex, echoHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact echoHeader.prepared.same
  · right; right; left
    have actualIndex := (observed.chooseRow.prepared_slot chooseHeader.prepared).2
    rw [same, ← actualIndex, chooseHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact chooseHeader.prepared.same
  · right; right; right;
    have actualIndex := (observed.selectRow.prepared_slot selectHeader.prepared).2
    rw [same, ← actualIndex, selectHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact selectHeader.prepared.same

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨ CallableIndexedNamedGeneration.source named = observed.echoRow.row.function.typedBody ∨ CallableIndexedNamedGeneration.source named = observed.chooseRow.row.function.typedBody ∨ CallableIndexedNamedGeneration.source named = observed.selectRow.row.function.typedBody := by
  rcases observed.cached_rows makeHeader echoHeader chooseHeader selectHeader selected with same | same | same | same
  · left
    exact congrArg (fun row => row.function.typedBody) same
  · right; left
    exact congrArg (fun row => row.function.typedBody) same
  · right; right; left
    exact congrArg (fun row => row.function.typedBody) same
  · right; right; right;
    exact congrArg (fun row => row.function.typedBody) same

theorem ObservedProgram.cached_assumptions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized.assumptions = [] := by
  rcases observed.cached_rows makeHeader echoHeader chooseHeader selectHeader selected with same | same | same | same
  · rw [same]; exact observed.makeRow.assumptions
  · rw [same]; exact observed.echoRow.assumptions
  · rw [same]; exact observed.chooseRow.assumptions
  · rw [same]; exact observed.selectRow.assumptions

theorem ObservedProgram.echo_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.echoRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.echoNodes, IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.echoShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.choose_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.chooseRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.chooseNodes, IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.chooseShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.select_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.selectRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.selectNodes, SelectShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same
  all_goals try cases same
  · rw [observed.selectShape.tableRead.form] at form; cases form
  · rw [observed.selectShape.base.calleeForm] at form; cases form
  · rw [observed.selectShape.base.form] at form; cases form
  · rw [observed.selectShape.keyRead.form] at form; cases form
  · rw [observed.selectShape.lookup.calleeForm] at form; cases form
  · rw [observed.selectShape.lookup.form] at form; cases form
  · rw [observed.selectShape.form] at form; cases form
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
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
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
      rcases observed.cached_source makeHeader echoHeader chooseHeader selectHeader support.caller.selected with original | original | original | original
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.echo_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.choose_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.select_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)

    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
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

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

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


structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  makeInput : Input fixture.recipe.compiled
  echoInput : Input fixture.recipe.compiled
  chooseInput : Input fixture.recipe.compiled
  selectInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  echoRow : echoInput.row = observed.echoRow.row
  chooseRow : chooseInput.row = observed.chooseRow.row
  selectRow : selectInput.row = observed.selectRow.row
  makePacket : Issued makeInput
  echoPacket : Issued echoInput
  choosePacket : Issued chooseInput
  selectPacket : Issued selectInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  echoHeader : ActualHeader fixture observed.echoRow.row
  chooseHeader : ActualHeader fixture observed.chooseRow.row
  selectHeader : ActualHeader fixture observed.selectRow.row
  makeEq : makeHeader.header = makePacket.header
  echoEq : echoHeader.header = echoPacket.header
  chooseEq : chooseHeader.header = choosePacket.header
  selectEq : selectHeader.header = selectPacket.header
  rows : Inventory [makeInput, echoInput, chooseInput, selectInput]
  rowsEq : rows = .cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket (.nil))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, echoInput, chooseInput, selectInput].map (fun input => input.prepared.index)).Nodup
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  echoDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named echoHeader.header.named.signature.key)
  chooseDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseHeader.header.named.signature.key)
  selectDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named selectHeader.header.named.signature.key)
theorem OrdinaryInventory.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture}
    (support : OrdinaryInventory fixture observed) :
    headers support.rows = [support.makeHeader.header, support.echoHeader.header, support.chooseHeader.header, support.selectHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.makeEq, support.echoEq, support.chooseEq, support.selectEq]

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨makeInput, echoInput, chooseInput, selectInput, makeRow, echoRow, chooseRow, selectRow, makePacket, echoPacket, choosePacket, selectPacket, makeHeader, echoHeader, chooseHeader, selectHeader, makeEq, echoEq, chooseEq, selectEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, echoInput, chooseInput, selectInput] :=
    .cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket (.nil))))
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have echoIndex : echoHeader.header.slot = observed.echoRow.index :=
    echoHeader.aligned.slot.trans (observed.echoRow.prepared_slot echoHeader.prepared).2
  have echoInputIndex : echoHeader.header.slot = echoInput.prepared.index := by
    rw [echoEq]; exact echoPacket.aligned.slot
  have chooseIndex : chooseHeader.header.slot = observed.chooseRow.index :=
    chooseHeader.aligned.slot.trans (observed.chooseRow.prepared_slot chooseHeader.prepared).2
  have chooseInputIndex : chooseHeader.header.slot = chooseInput.prepared.index := by
    rw [chooseEq]; exact choosePacket.aligned.slot
  have selectIndex : selectHeader.header.slot = observed.selectRow.index :=
    selectHeader.aligned.slot.trans (observed.selectRow.prepared_slot selectHeader.prepared).2
  have selectInputIndex : selectHeader.header.slot = selectInput.prepared.index := by
    rw [selectEq]; exact selectPacket.aligned.slot
  have makeEcho : makeHeader.header.slot ≠ echoHeader.header.slot := by
    rw [makeIndex, echoIndex]; exact observed.makeEcho
  have makeEchoInput : makeInput.prepared.index ≠ echoInput.prepared.index := by
    rw [← makeInputIndex, ← echoInputIndex]; exact makeEcho
  have makeChoose : makeHeader.header.slot ≠ chooseHeader.header.slot := by
    rw [makeIndex, chooseIndex]; exact observed.makeChoose
  have makeChooseInput : makeInput.prepared.index ≠ chooseInput.prepared.index := by
    rw [← makeInputIndex, ← chooseInputIndex]; exact makeChoose
  have makeSelect : makeHeader.header.slot ≠ selectHeader.header.slot := by
    rw [makeIndex, selectIndex]; exact observed.makeSelect
  have makeSelectInput : makeInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← makeInputIndex, ← selectInputIndex]; exact makeSelect
  have echoChoose : echoHeader.header.slot ≠ chooseHeader.header.slot := by
    rw [echoIndex, chooseIndex]; exact observed.echoChoose
  have echoChooseInput : echoInput.prepared.index ≠ chooseInput.prepared.index := by
    rw [← echoInputIndex, ← chooseInputIndex]; exact echoChoose
  have echoSelect : echoHeader.header.slot ≠ selectHeader.header.slot := by
    rw [echoIndex, selectIndex]; exact observed.echoSelect
  have echoSelectInput : echoInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← echoInputIndex, ← selectInputIndex]; exact echoSelect
  have chooseSelect : chooseHeader.header.slot ≠ selectHeader.header.slot := by
    rw [chooseIndex, selectIndex]; exact observed.chooseSelect
  have chooseSelectInput : chooseInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← chooseInputIndex, ← selectInputIndex]; exact chooseSelect
  exact ⟨{
    makeInput := makeInput
    echoInput := echoInput
    chooseInput := chooseInput
    selectInput := selectInput
    makeRow := makeRow
    echoRow := echoRow
    chooseRow := chooseRow
    selectRow := selectRow
    makePacket := makePacket
    echoPacket := echoPacket
    choosePacket := choosePacket
    selectPacket := selectPacket
    makeHeader := makeHeader
    echoHeader := echoHeader
    chooseHeader := chooseHeader
    selectHeader := selectHeader
    makeEq := makeEq
    echoEq := echoEq
    chooseEq := chooseEq
    selectEq := selectEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [makeEchoInput, makeChooseInput, makeSelectInput, echoChooseInput, echoSelectInput, chooseSelectInput]
    makeDescriptor := makeHeader.descriptor makeStages
    echoDescriptor := echoHeader.descriptor echoStages
    chooseDescriptor := chooseHeader.descriptor chooseStages
    selectDescriptor := selectHeader.descriptor selectStages
  }⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexProgramCertificate
/-! The original recursive index program is admitted once from its complete actual
cache. A finite row check selects the existing four-header order; it does not
construct syntax, metadata, closure support or method body support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate
  rows : ∀ row ∈ certificate.table.rows, row ∈ [observed.makeRow.row, observed.echoRow.row, observed.chooseRow.row, observed.selectRow.row]

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original recursive index program certification rejected")
  | some certificate =>
      if rows : certificate.table.rows.all (fun row =>
          [observed.makeRow.row, observed.echoRow.row, observed.chooseRow.row, observed.selectRow.row].any (fun expected => row == expected)) = true then
        pure ⟨certificate, accepted, by
          intro row member
          obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
          exact (eq_of_beq same).symm ▸ present⟩
      else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.echoInput, inventory.chooseInput, inventory.selectInput] admission.certificate.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeRow⟩
  · exact ⟨inventory.echoInput, by simp, inventory.echoRow⟩
  · exact ⟨inventory.chooseInput, by simp, inventory.chooseRow⟩
  · exact ⟨inventory.selectInput, by simp, inventory.selectRow⟩

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
the nine-call regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

abbrev ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) :=
  CoreLowering.RecursiveNamedPublicPhysicalSessionState.Call session key arguments runOptions

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
      return ⟨⟨checkpoint, started⟩, completion, result ▸ executed.property⟩

abbrev ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) :=
  CoreLowering.RecursiveNamedPublicPhysicalSessionState.FunctionCall session key arguments runOptions

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


def firstKey : Core.Word := Core.Word.ofNatModulo 1
def secondKey : Core.Word := Core.Word.ofNatModulo 2
def missingKey : Core.Word := Core.Word.ofNatModulo 3

def table (first second : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .mapping .word closureType [(.word firstKey, .function first), (.word secondKey, .function second)]

structure ObservedFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt key arguments runOptions (.ok (.failed reason returned))
  diagnostic : SourceCoreFaultSites.Diagnostic
  decoded : checkpoint.diagnostic reason = .ok (some diagnostic)

def observeFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFailure session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .ok (.failed reason returned) =>
      match decoded : checkpoint.diagnostic reason with
      | .ok (some diagnostic) => return ⟨checkpoint, started, reason, returned, result ▸ executed.property, diagnostic, decoded⟩
      | _ => throw (IO.userError "missing-key failure had no actual diagnostic")
    | _ => throw (IO.userError "missing-key call unexpectedly succeeded")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  firstSelect : ObservedFunctionCall second.completion.session observed.selectRow.row.key [table first.handle second.handle, .word firstKey]
  firstSame : firstSelect.handle = first.handle
  firstRead : ObservedInvocation firstSelect.completion.session firstSelect.handle .unit
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
  secondSelect : ObservedFunctionCall intervening.completion.session observed.selectRow.row.key [table first.handle second.handle, .word secondKey]
  secondSame : secondSelect.handle = second.handle
  secondRead : ObservedInvocation secondSelect.completion.session secondSelect.handle .unit
  secondValue : secondRead.completion.value = .word secondSeed
  failed : ObservedFailure secondRead.completion.session observed.selectRow.row.key [table first.handle second.handle, .word missingKey]
  missingDiagnostic : failed.diagnostic = {
    error := .typeMismatch closureType none
    site := .occurrence observed.selectShape.value.node.id.occurrence
    span := some observed.selectShape.value.node.span }
  repeatedRead : ObservedInvocation failed.returned first.handle .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let firstSelect ← observeFunctionCall second.completion.session observed.selectRow.row.key [table first.handle second.handle, .word firstKey]
    if firstSame : firstSelect.handle = first.handle then
      let firstRead ← observeInvocation firstSelect.completion.session firstSelect.handle .unit
      if firstValue : firstRead.completion.value = .word seed then
        let intervening ← observeFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
        let secondSelect ← observeFunctionCall intervening.completion.session observed.selectRow.row.key [table first.handle second.handle, .word secondKey]
        if secondSame : secondSelect.handle = second.handle then
          let secondRead ← observeInvocation secondSelect.completion.session secondSelect.handle .unit
          if secondValue : secondRead.completion.value = .word secondSeed then
            let failed ← observeFailure secondRead.completion.session observed.selectRow.row.key [table first.handle second.handle, .word missingKey]
            if missingDiagnostic : failed.diagnostic = {
                error := .typeMismatch closureType none
                site := .occurrence observed.selectShape.value.node.id.occurrence
                span := some observed.selectShape.value.node.span } then
              let repeatedRead ← observeInvocation failed.returned first.handle .unit
              if repeatedValue : repeatedRead.completion.value = .word seed then
                return ⟨first, second, distinct, firstSelect, firstSame, firstRead, firstValue,
                  intervening, secondSelect, secondSame, secondRead, secondValue, failed, missingDiagnostic, repeatedRead, repeatedValue⟩
              else throw (IO.userError "old handle changed after missing-key failure")
            else throw (IO.userError "missing-key diagnostic did not name the original index occurrence")
          else throw (IO.userError "second selected capture not20")
        else throw (IO.userError "second key selected the wrong handle")
      else throw (IO.userError "first selected capture not10")
    else throw (IO.userError "first key selected the wrong handle")
  else throw (IO.userError "initial exports lost distinct captures")

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSelectSupport
/-! Finite original Source facts for recursive index and its direct declaration children. The
synthetic callee references carry static catalog metadata; only the original
ordered argument expressions are evaluated recursively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem select_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.selectRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.selectShape.tableRead.node ∨
      node = observed.selectShape.base.callee.node ∨
      node = observed.selectShape.base.value.node ∨
      node = observed.selectShape.keyRead.node ∨
      node = observed.selectShape.lookup.callee.node ∨
      node = observed.selectShape.lookup.value.node ∨
      node = observed.selectShape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.selectNodes] at present
  simpa only [SelectShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.select_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row)
    (named : CallableIndexedNamedGeneration.Named) (same : named.specialized = observed.selectRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.tableRead.requirements
    · exact observed.selectShape.base.callee.requirements
    · exact observed.selectShape.base.value.requirements
    · exact observed.selectShape.keyRead.requirements
    · exact observed.selectShape.lookup.callee.requirements
    · exact observed.selectShape.lookup.value.requirements
    · exact observed.selectShape.value.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.tableRead.coercions
    · exact observed.selectShape.base.callee.coercions
    · exact observed.selectShape.base.value.coercions
    · exact observed.selectShape.keyRead.coercions
    · exact observed.selectShape.lookup.callee.coercions
    · exact observed.selectShape.lookup.value.coercions
    · exact observed.selectShape.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.selectShape.tableRead.form] at form; cases form
    · rw [observed.selectShape.base.calleeForm] at form; cases form
    · rw [observed.selectShape.base.form] at form; cases form
    · rw [observed.selectShape.keyRead.form] at form; cases form
    · rw [observed.selectShape.lookup.calleeForm] at form; cases form
    · rw [observed.selectShape.lookup.form] at form; cases form
    · rw [observed.selectShape.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    rw [same]; exact observed.selectRow.assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.select_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row) :
    GeneralSyntax actual.header.function.source observed.selectShape.value.node.id := by
  rw [actual.source]
  refine .index observed.selectShape.value.found observed.selectShape.form
    observed.selectShape.lookup.value.found ?_ ?_
  · refine .direct observed.selectShape.base.value.found observed.selectShape.base.form ?_ ?_
    · rw [observed.selectShape.base.exact]; exact ⟨rfl, rfl⟩
    · intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.read observed.selectShape.tableRead.found observed.selectShape.tableRead.form)
  · refine .direct observed.selectShape.lookup.value.found observed.selectShape.lookup.form ?_ ?_
    · rw [observed.selectShape.lookup.exact]; exact ⟨rfl, rfl⟩
    · intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.read observed.selectShape.keyRead.found observed.selectShape.keyRead.form)

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.select_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row)
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
      terminal.expression = observed.selectShape.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.selectShape.value.node.id
    observed.selectShape.statement observed.selectShape.roots observed.selectShape.statementFound observed.selectShape.statementForm
  have same : terminal.prepared.named.specialized = observed.selectRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (actual.select_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.select_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
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
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have headerKey := (selected_key selected).trans key
  have member : header ∈ [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · exact same
  · rw [same, echoHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.echoRow observed.makeEcho headerKey.symm)
  · rw [same, chooseHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.chooseRow observed.makeChoose headerKey.symm)
  · rw [same, selectHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.selectRow observed.makeSelect headerKey.symm)

theorem selected_select_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] root header)
    (key : root.key = observed.selectRow.row.key) : header = selectHeader.header := by
  have headerKey := (selected_key selected).trans key
  have member : header ∈ [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · rw [same, makeHeader.key] at headerKey
    exact False.elim (observed.makeRow.keys_ne observed.selectRow observed.makeSelect headerKey)
  · rw [same, echoHeader.key] at headerKey
    exact False.elim (observed.echoRow.keys_ne observed.selectRow observed.echoSelect headerKey)
  · rw [same, chooseHeader.key] at headerKey
    exact False.elim (observed.chooseRow.keys_ne observed.selectRow observed.chooseSelect headerKey)
  · exact same

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
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root makeHeader echoHeader chooseHeader selectHeader request.selected (started_key request)

theorem selected_select_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (echoHeader : ActualHeader fixture observed.echoRow.row)
    (chooseHeader : ActualHeader fixture observed.chooseRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.selectRow.row.key arguments fuel world store) : request.header = selectHeader.header := by
  subst headers
  exact selected_select_root makeHeader echoHeader chooseHeader selectHeader request.selected (started_key request)

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

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
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
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.echo_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [containerType] := by
  have raw := (observed.echoRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.echoShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.echo_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) : actual.header.types = [containerType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.echo_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.echo_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.echoRow.row) : actual.header.function.resultType = containerType := by
  have result := (observed.echoRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.echoShape.returns]
  rfl

theorem ActualHeader.choose_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.chooseRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.chooseShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.choose_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.choose_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.choose_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.chooseRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.chooseRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.chooseShape.returns]
  rfl

theorem ActualHeader.select_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [containerType, .word] := by
  have raw := (observed.selectRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.tail _ (.head _)))) actual).1
  rw [observed.selectShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.select_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) : actual.header.types = [containerType, .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.select_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.select_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.selectRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.tail _ (.head _)))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.selectShape.returns]
  rfl

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexCertifiedHeaders
/-! The original physical cache slot identifies each automatic catalog Header.
The original public observations retain their complete execution receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open SelectedCompilationCertifiedPublicSession (EligibleRow Profiled Initial)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem selected_row (row : ObservedRow fixture signature) :
    ∃ selected : EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨_signatureEq, indexEq⟩ := row.prepared_slot prepared
  refine ⟨⟨prepared.named, row.index, row.global, indexEq ▸ prepared.selected,
    row.slot, row.globalKey, ?_⟩, prepared.same⟩
  rw [prepared.same]
  refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  simp only [row.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
    List.not_mem_nil, false_implies, implies_true]

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (specialized : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans specialized)
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation,
      sameRow, row.parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

def firstCall {row : ObservedRow fixture signature} (first : ObservedPublicRun fixture row) :
    SelectedCompilationPublicSessionState.FunctionCall first.session row.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

def functionCall {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments) :
    SelectedCompilationPublicSessionState.FunctionCall session key arguments runOptions :=
  ⟨⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩, call.handle, call.returned⟩

/-- The first successful export keeps the actual requested raw function type. -/
theorem initial_handle_type {issued : Profiled fixture.recipe}
    {row : ObservedRow fixture signature} {first : ObservedPublicRun fixture row}
    (initial : Initial issued.toIssued (firstCall first).toCall.toStartedCall) :
    first.handle.sourceType = initial.header.function.resultType := by
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨_actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded initial.start.atCheckpoint
  have atRecipe : initial.start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ initial.start.started.recipe_eq
  have requested := initial.start.started.original.result_type_at atRecipe initial.start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result initial.start.selected).2
  rw [resultType] at requested
  exact exported.function_source_type requested (valueEq.symm.trans first.returned)

end Tests.SourceCoreRecursiveIndex.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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
    headers support.rows = [support.makeHeader.header, support.echoHeader.header, support.chooseHeader.header, support.selectHeader.header] :=
  support.toOrdinaryInventory.header_list

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed makeStages echoStages chooseStages selectStages
  obtain ⟨program⟩ := admission.certificate.issue_for_without_methods fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    inventory.rows (admission.aligned inventory)
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)
  exact ⟨{toOrdinaryInventory := inventory, program := program}⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexInputs
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def sourceTable (first second : Entry) : Dynamic.Value :=
  .mapping .word closureType [(.word firstKey, first.source), (.word secondKey, second.source)]

theorem word_input {entries : List Entry} {context : SourceSemantics.Context} (word : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context .word (.word word) (.word word) :=
  .data ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩

theorem table_input {entries : List Entry} {context : SourceSemantics.Context}
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context containerType
      (table firstHandle secondHandle) (sourceTable first second) := by
  have firstInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) first firstMember
  have secondInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) second secondMember
  rw [firstType, firstHandleEq] at firstInput
  rw [secondType, secondHandleEq] at secondInput
  exact .mapping (.entry (word_input firstKey) firstInput
    (.entry (word_input secondKey) secondInput (.empty _ _)))

theorem select_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [containerType, .word]
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] :=
  .cons (table_input first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq)
    (.cons (word_input key) .nil)

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexCertifiedMeaning
/-! The original indexed closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original index compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) where
  initial : Initial issued.toIssued (firstCall first).toCall.toStartedCall
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = first.handle
  handleType : first.handle.sourceType = closureType
  after : issued.toIssued.State initial.header first.completion.session [entry]
  trace : SelectedCompilationPublicSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Profiled fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure FunctionMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session row.row.key publicArguments)
    (arguments : List Dynamic.Value) (scope : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key publicArguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = closureType
  after : issued.toIssued.State anchor call.completion.session (entries ++ [entry])
  trace : SelectedCompilationPublicSessionState.SourceCall anchor request.header scope before.heap arguments (.value entry.source) after.heap

theorem unit_input (entries : List Entry) (context : SourceSemantics.Context) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context .unit .unit .unit :=
  .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
    ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩

structure InvocationMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (entry : Entry)
    {handle : SourceCorePublicValues.Handle}
    (call : ObservedInvocation session handle .unit)
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = handle
  handleType : handle.sourceType = closureType
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments .unit
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.toIssued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    (firstCall first).toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := firstCall first) (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  have raw : initial.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, type.trans raw, handle,
    (initial_handle_type initial).trans raw, after, trace⟩⟩⟩

theorem make_meaning (before : issued.toIssued.State anchor session entries)
    (value : Core.Word) (call : ObservedFunctionCall session observed.makeRow.row.key [.word value])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FunctionMeaning issued before observed.makeRow call [.word value] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call.toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value] := by
    rw [← actualEq, actual.make_input_types_source]
    exact .cons (word_input value) .nil
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.toIssued.reflect_function before call request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

theorem invocation_meaning (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = closureType)
    (call : ObservedInvocation session handle .unit)
    (word : Core.Word) (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (InvocationMeaning issued before entry call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType)
      (unit_input entries anchor.function.context)
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, handleType, arguments, packing, arity, after, size, trace⟩⟩

theorem FirstMeaning.forward {stages : ObservedStages fixture observed.makeRow}
    {first : ObservedPublicRun fixture observed.makeRow} (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support (firstCall first).toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed] meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact meaning.initial.forward_function
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
    (parameter := .unit) (resultType := .word)
    (by rw [meaning.headerEq, meaning.actual.make_result_type]; rfl) meaning.trace

theorem FunctionMeaning.forward {before : issued.toIssued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session row.row.key publicArguments}
    {arguments : List Dynamic.Value} {scope : Staging.Recursive.Scope}
    (meaning : FunctionMeaning issued before row call arguments scope) (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      call.toCall.toStartedCall .unit .word meaning.entry.source meaning.after.heap :=
  issued.toIssued.forward_function before call.toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem InvocationMeaning.forward {before : issued.toIssued.State anchor session entries}
    {entry : Entry} {word : Core.Word} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle .unit} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry call word scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (.word word) checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectScalarForward.forward_call issued.support issued.prepared
    before entry meaning.member (.word word) meaning.entryType (meaning.handleEq ▸ meaning.handleType)
    (unit_input entries anchor.function.context)
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreRecursiveIndex.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexFailureStep
/-! The failed index call keeps the exact current encoder registry and all
older handle captures. The Source failure remains related to the actual token;
no injectivity assumption about diagnostic tokens is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {entries : List Entry}

/-- The actual failed public call retains export authority for the next call. -/
theorem ObservedFailure.exportsReady {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session key arguments) (ready : session.ExportsReady) :
    call.returned.ExportsReady := by
  have compiledAt : ∃ compiled, artifact.CompiledAt compiled := by
    rcases artifact with ⟨compiled, opened⟩
    exact ⟨compiled, rfl⟩
  obtain ⟨compiled, compiledAt⟩ := compiledAt
  obtain ⟨checkpoint, started, resumed⟩ := call.executed
  obtain ⟨_recipe, _native, indexedSession, indexedCheckpoint, _opened, atSession, atCheckpoint, actualStart⟩ :=
    SourceCoreExecution.Session.start_indexed (compiled := compiled) compiledAt started
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ :=
    resumed.indexed_failed atCheckpoint
  exact returnedAt.exportsReady_iff.mpr (failed.exportsReady
    ((indexedSession.start_root_receipt actualStart).initial_registry.exportsReady
      (atSession.exportsReady_iff.mp ready)))

theorem RetainedState.select_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.returned entries, ∃ failure,
      SourceCall support support.selectHeader.header invocation state.heap
        [sourceTable first second, .word key] (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
        failure call.reason := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]
    support.rows support.complete state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader
    support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.selectDescriptor
  let started : RecursiveNamedPublicPhysicalSessionState.StartedCall session observed.selectRow.row.key
      [table firstHandle secondHandle, .word key] runOptions := ⟨call.checkpoint, call.started⟩
  obtain ⟨failure, after, trace, decoded⟩ :=
    RecursiveNamedPublicPhysicalSessionFailureStep.State.failed_call_at_input_registry
      support.program fixture.recipePrepared state started call.returned call.reason call.executed
      request inputs descriptor invocation
  exact ⟨after, failure, by simpa only [selected] using trace, decoded⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexCertifiedSelection
/-! Mapping inputs refer to the actual retained handles. Successful selections
append their real exports; a failed selection retains every prior entry and its
reached Source heap, together with the original public diagnostic relation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Profiled fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem select_meaning (before : issued.toIssued.State anchor session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word)
    (call : ObservedFunctionCall session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FunctionMeaning issued before observed.selectRow call [sourceTable first second, .word key] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.selectRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call.toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.selectRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [← actualEq, actual.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.select_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.toIssued.reflect_function before call request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

def failureCall {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session key arguments) :
    SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions :=
  ⟨call.checkpoint, call.started⟩

structure FailureMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session observed.selectRow.row.key publicArguments)
    (arguments : List Dynamic.Value) (scope : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.selectRow.row.key publicArguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.selectRow.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  failure : Staging.Recursive.Failure
  after : issued.toIssued.State anchor call.returned entries
  trace : SelectedCompilationPublicSessionState.SourceCall anchor request.header scope
    before.heap arguments (.fault failure) after.heap
  diagnostic : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
    after.receiving.result.diagnostics failure call.reason

theorem failure_meaning (before : issued.toIssued.State anchor session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word)
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FailureMeaning issued before call [sourceTable first second, .word key] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.selectRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before (failureCall call) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.selectRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [← actualEq, actual.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  obtain ⟨failure, after, trace, diagnostic⟩ := issued.reflect_failure before (failureCall call)
    call.returned call.reason call.executed request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, failure, after, trace, diagnostic⟩⟩

theorem FailureMeaning.forward {before : issued.toIssued.State anchor session entries}
    {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFailure session observed.selectRow.row.key publicArguments}
    {arguments : List Dynamic.Value} {scope : Staging.Recursive.Scope}
    (meaning : FailureMeaning issued before call arguments scope) (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      meaning.failure (failureCall call) meaning.after.heap :=
  issued.forward_failure before (failureCall call) meaning.request meaning.inputs ready meaning.trace

end Tests.SourceCoreRecursiveIndex.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexCompilerProfile
/-! The original mapping sequence uses one automatic compiler profile and
catalog. A missing key retains all five exports, their captures and the reached
Source heap, from which the original first handle is invoked again. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  second : FunctionMeaning issued first.after observed.makeRow sequence.second [.word secondSeed]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  firstSelect : FunctionMeaning issued second.after observed.selectRow sequence.firstSelect
    [sourceTable first.entry second.entry, .word firstKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  firstRead : InvocationMeaning issued firstSelect.after firstSelect.entry sequence.firstRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : FunctionMeaning issued firstRead.after observed.makeRow sequence.intervening [.word interveningSeed]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  secondSelect : FunctionMeaning issued intervening.after observed.selectRow sequence.secondSelect
    [sourceTable first.entry second.entry, .word secondKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  secondRead : InvocationMeaning issued secondSelect.after secondSelect.entry sequence.secondRead secondSeed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  failed : FailureMeaning issued secondRead.after sequence.failed
    [sourceTable first.entry second.entry, .word missingKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  repeatedRead : InvocationMeaning issued failed.after first.entry sequence.repeatedRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Profiled fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.selected_handles (meaning : SequenceMeaning issued stages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
    meaning.firstSelect.entry.handle = meaning.first.entry.handle ∧
    meaning.secondSelect.entry.handle = meaning.second.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq, meaning.firstSelect.handleEq, meaning.secondSelect.handleEq]
  exact ⟨sequence.distinct, sequence.firstSame, sequence.secondSame⟩

theorem SequenceMeaning.original_diagnostic (_meaning : SequenceMeaning issued stages sequence) :
    sequence.failed.checkpoint.diagnostic sequence.failed.reason = .ok (some {
      error := .typeMismatch closureType none
      site := .occurrence observed.selectShape.value.node.id.occurrence
      span := some observed.selectShape.value.node.span }) := by
  rw [sequence.failed.decoded, sequence.missingDiagnostic]

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Profiled fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨second⟩ := make_meaning first.after secondSeed sequence.second scope
  obtain ⟨firstSelect⟩ := select_meaning second.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq firstKey sequence.firstSelect scope
  obtain ⟨firstRead⟩ := invocation_meaning firstSelect.after firstSelect.entry (by simp)
    firstSelect.entryType firstSelect.handleEq firstSelect.handleType sequence.firstRead seed sequence.firstValue scope
  obtain ⟨intervening⟩ := make_meaning firstRead.after interveningSeed sequence.intervening scope
  obtain ⟨secondSelect⟩ := select_meaning intervening.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq secondKey sequence.secondSelect scope
  obtain ⟨secondRead⟩ := invocation_meaning secondSelect.after secondSelect.entry (by simp)
    secondSelect.entryType secondSelect.handleEq secondSelect.handleType sequence.secondRead secondSeed sequence.secondValue scope
  obtain ⟨failed⟩ := failure_meaning secondRead.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq missingKey sequence.failed scope
  obtain ⟨repeatedRead⟩ := invocation_meaning failed.after first.entry (by simp)
    first.entryType first.handleEq first.handleType sequence.repeatedRead seed sequence.repeatedValue scope
  exact ⟨issued, ⟨⟨first, second, firstSelect, firstRead, intervening, secondSelect, secondRead, failed, repeatedRead⟩⟩⟩

/-- Every completed ordinary application keeps the same arguments, callable
value, full dictionary and heap. A staging rejection keeps its actual guard. -/
structure PlainMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.first.after.heap [.word secondSeed] meaning.second.entry.source meaning.second.after.heap
  firstSelect : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.firstSelect.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.second.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word firstKey]
    meaning.firstSelect.entry.source meaning.firstSelect.after.heap
  firstRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.firstSelect.entry.source)
    meaning.firstSelect.after.heap meaning.firstSelect.entry.source meaning.firstRead.arguments
    (.word seed) meaning.firstRead.after.heap
  intervening : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.intervening.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.firstRead.after.heap [.word interveningSeed] meaning.intervening.entry.source meaning.intervening.after.heap
  secondSelect : SelectedCompilationPublicSessionState.PlainValue meaning.first.initial.header meaning.secondSelect.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.intervening.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word secondKey]
    meaning.secondSelect.entry.source meaning.secondSelect.after.heap
  secondRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.secondSelect.entry.source)
    meaning.secondSelect.after.heap meaning.secondSelect.entry.source meaning.secondRead.arguments
    (.word secondSeed) meaning.secondRead.after.heap
  failed : SelectedCompilationPublicSessionState.FailureProjection
    meaning.first.initial.header meaning.failed.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.secondRead.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word missingKey]
    meaning.failed.failure meaning.failed.after.heap
  repeatedRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.first.entry.source)
    meaning.failed.after.heap meaning.first.entry.source meaning.repeatedRead.arguments
    (.word seed) meaning.repeatedRead.after.heap

theorem SequenceMeaning.plain (meaning : SequenceMeaning issued stages sequence) : PlainMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, meaning.firstSelect.trace.value_plain,
    meaning.firstRead.trace.sound.value_plain, meaning.intervening.trace.value_plain,
    meaning.secondSelect.trace.value_plain, meaning.secondRead.trace.sound.value_plain,
    meaning.failed.trace.failure_plain, meaning.repeatedRead.trace.sound.value_plain⟩

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.second.toCall.toStartedCall .unit .word meaning.second.entry.source meaning.second.after.heap
  firstSelect : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt
    (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.firstSelect.toCall.toStartedCall .unit .word meaning.firstSelect.entry.source meaning.firstSelect.after.heap
  firstRead : ∃ checkpoint, sequence.firstSelect.completion.session.startHandlePacked sequence.firstSelect.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry])
      (.word seed) checkpoint meaning.firstRead.after.heap
  intervening : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.intervening.toCall.toStartedCall .unit .word meaning.intervening.entry.source meaning.intervening.after.heap
  secondSelect : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt
    (entries := (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.secondSelect.toCall.toStartedCall .unit .word meaning.secondSelect.entry.source meaning.secondSelect.after.heap
  secondRead : ∃ checkpoint, sequence.secondSelect.completion.session.startHandlePacked sequence.secondSelect.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry] ++ [meaning.secondSelect.entry])
      (.word secondSeed) checkpoint meaning.secondRead.after.heap
  failed : SelectedCompilationPublicSessionFailureForward.FailureForwardAt
    (entries := ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry]) ++ [meaning.secondSelect.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    meaning.failed.failure (failureCall sequence.failed) meaning.failed.after.heap
  repeatedRead : ∃ checkpoint, sequence.failed.returned.startHandlePacked sequence.first.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry] ++ [meaning.secondSelect.entry])
      (.word seed) checkpoint meaning.repeatedRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  have failedReady := sequence.failed.exportsReady secondReadReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstSelect.forward secondReady,
    meaning.firstRead.forward firstSelectReady, meaning.intervening.forward firstReadReady,
    meaning.secondSelect.forward interveningReady, meaning.secondRead.forward secondSelectReady,
    meaning.failed.forward secondReadReady, meaning.repeatedRead.forward failedReady⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Profiled fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.firstSelect.entry.handle = meaning.first.entry.handle ∧
      meaning.secondSelect.entry.handle = meaning.second.entry.handle ∧
      ForwardMeaning meaning ∧ PlainMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  obtain ⟨distinct, firstSame, secondSame⟩ := meaning.selected_handles
  exact ⟨issued, meaning, distinct, firstSame, secondSame, meaning.forward, meaning.plain⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 4 && profile.value.table.rows.length == 4 do
    throw (IO.userError "index profile changed original cache4/table4")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstSelect.completion.session.heapSize,
    sequence.firstRead.completion.session.heapSize, sequence.intervening.completion.session.heapSize,
    sequence.secondSelect.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.failed.returned.heapSize, sequence.repeatedRead.completion.session.heapSize]
  unless stores == [5,11,17,31,34,40,54,57,71,74] do
    throw (IO.userError s!"index profile stores changed: {reprStr stores}")
  IO.println s!"INDEX_COMPILER_PROFILE_FORWARD_PASS: original checker1000/cache4/table4; one complete profile and automatic catalog; original nine operations, independent Dynamic outcomes and all sufficient public fuel bounds; mapping selections A10/B20; missing-key diagnostic; old A10 after failure; stores {reprStr stores}"

end Tests.SourceCoreRecursiveIndex.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexFailureForward
/-! Independent Source failure fixes a sufficient execution budget at the
original public checkpoint. Every output budget, including zero, retains the
same reached Source heap, current diagnostic registry and earlier handles. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {entries : List Entry}

def ForwardFailureAt (support : PublicSupports receiver)
    {firstHandle secondHandle : SourceCorePublicValues.Handle} {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (entries : List Entry) : Prop :=
  ∃ token required,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      required ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ state : RetainedState support returned entries, state.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics failure token

theorem forward_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.fault failure) after) :
    ForwardFailureAt support call failure after entries := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]
    support.rows support.complete state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader
    support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  let started : RecursiveNamedPublicPhysicalSessionState.StartedCall session observed.selectRow.row.key
      [table firstHandle secondHandle, .word key] runOptions := ⟨call.checkpoint, call.started⟩
  obtain ⟨required, token, enough⟩ :=
    RecursiveNamedPublicPhysicalSessionFailureForward.forward_call_at_input_registry
      support.program fixture.recipePrepared state started request inputs ready (by simpa only [selected] using trace)
  exact ⟨token, required, enough⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
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
  obtain ⟨sources, packing, _arity, after, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar
      support.program fixture.recipePrepared state entry member (.word word)
      entryType (entryHandle ▸ handleType) input
      (by simpa only [entryHandle] using call.executed) returned invocation
  exact ⟨sources, after, packing, size, trace⟩


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
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨sources, packing, _arity, source, after, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectSuccessStep.State.invoke_success
      support.program fixture.recipePrepared state entry member entryType input
      (by simpa only [entryHandle] using call.executed) invocation
  exact ⟨sources, source, after, packing, size, trace⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexInvocationForward
/-! The three captured closure calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
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
  obtain ⟨size, trace⟩ := trace
  have forward := RecursiveNamedPublicPhysicalSessionDirectScalarForward.forward_call
    support.program fixture.recipePrepared state entry member (.word word)
    entryType (entryHandle ▸ handleType) unitInput
    (by simpa only [entryHandle] using accepted) exportsReady packing trace
  exact ⟨publicCheckpoint, accepted, forward⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
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
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_make_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.makeHeader.make_input_types_source]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.makeDescriptor
  obtain ⟨entry, type, handle, handleType, after, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle_at_input_registry
      support.program fixture.recipePrepared state call request inputs descriptor invocation
  have resultType : request.header.function.resultType = .function .unit .word := by
    rw [selected]
    exact support.makeHeader.make_result_type
  exact ⟨entry, type.trans resultType, handle, handleType.trans resultType, after,
    by simpa only [selected] using trace⟩

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.make
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.make_typed_handle call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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
      support.makeHeader support.echoHeader support.chooseHeader support.selectHeader (root := root) (header := selectedHeader)
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
    rw [support.makeHeader.make_types]
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
    first_meaning_typed_handle support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
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
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
    (first : ObservedPublicRun fixture observed.makeRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨start⟩ := first.initial_start support
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      support.makeHeader.header.function.context [.word seed] support.makeHeader.header.types := by
    rw [support.makeHeader.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have functionResult : SourceCoreRawMetadata.runtimeType support.makeHeader.header.function.resultType = .function .unit .word := by
    rw [support.makeHeader.make_result_type]
    rfl
  have forwarded := RecursiveNamedPublicPhysicalSessionInitialExportForward.first_function
    support.rows fixture.recipePrepared support.makeHeader.header support.makeHeader.header support.program
    support.distinct first.as_function_call.toCall.toStartedCall start
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings functionResult trace
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, InitialForwardAt, ReturnedValue,
    ObservedPublicRun.as_function_call, support.makeHeader.make_result_type] using forwarded

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSelectStep
/-! A genuine successful public selection extends the current retained
history with its actual selected closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public mapping selection constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.select_typed_handle
    (state : RetainedState support publicSession entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall publicSession observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.selectHeader.header invocation state.heap [sourceTable first second, .word key]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.selectDescriptor
  obtain ⟨entry, type, handle, handleType, after, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle_at_input_registry
      support.program fixture.recipePrepared state call request inputs descriptor invocation
  have resultType : request.header.function.resultType = .function .unit .word := by
    rw [selected]
    exact support.selectHeader.select_result_type
  exact ⟨entry, type.trans resultType, handle, handleType.trans resultType, after,
    by simpa only [selected] using trace⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexPublicExecution
/-! The same checked index expression selects two distinct retained closures,
fails for a third key, and leaves a session in which the first closure still runs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  firstSelected : Entry
  intervening : Entry
  secondSelected : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  firstSelectedType : firstSelected.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  secondSelectedType : secondSelected.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  firstSelectedHandle : firstSelected.handle = sequence.firstSelect.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  secondSelectedHandle : secondSelected.handle = sequence.secondSelect.handle
  firstHandleType : sequence.first.handle.sourceType = closureType
  firstSelectedHandleType : sequence.firstSelect.handle.sourceType = closureType
  secondSelectedHandleType : sequence.secondSelect.handle.sourceType = closureType
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstSelectState : RetainedState support sequence.firstSelect.completion.session [first, second, firstSelected]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second, firstSelected]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, firstSelected, intervening]
  secondSelectState : RetainedState support sequence.secondSelect.completion.session [first, second, firstSelected, intervening, secondSelected]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, firstSelected, intervening, secondSelected]
  failedState : RetainedState support sequence.failed.returned [first, second, firstSelected, intervening, secondSelected]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, firstSelected, intervening, secondSelected]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstSelectTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap [sourceTable first second, .word firstKey] (.value firstSelected.source) firstSelectState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstSelectState.heap firstSelected.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondSelectTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap [sourceTable first second, .word secondKey] (.value secondSelected.source) secondSelectState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondSelectState.heap secondSelected.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  failure : Staging.Recursive.Failure
  failedTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap [sourceTable first second, .word missingKey] (.fault failure) failedState.heap
  failedMeaning : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
    failedState.receiving.result.diagnostics failure sequence.failed.reason
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    failedState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports
    fixture observed admission makeStages echoStages chooseStages selectStages receiver
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, _secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second scope
  obtain ⟨firstSelected, firstSelectedType, firstSelectedHandle, firstSelectedHandleType, firstSelectState, firstSelectTrace⟩ :=
    secondState.select_typed_handle first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.firstSelect scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word firstSelectState firstSelected
    (by simp) firstSelectedType firstSelectedHandle firstSelectedHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.make_typed_handle sequence.intervening scope
  obtain ⟨secondSelected, secondSelectedType, secondSelectedHandle, secondSelectedHandleType, secondSelectState, secondSelectTrace⟩ :=
    interveningState.select_typed_handle first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.secondSelect scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word secondSelectState secondSelected
    (by simp) secondSelectedType secondSelectedHandle secondSelectedHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨failedState, failure, failedTrace, failedMeaning⟩ :=
    secondReadState.select_failure first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.failed scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word failedState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, firstSelected, intervening, secondSelected,
    firstType, secondType, firstSelectedType, interveningType, secondSelectedType,
    firstHandle, secondHandle, firstSelectedHandle, interveningHandle, secondSelectedHandle,
    firstHandleType, firstSelectedHandleType, secondSelectedHandleType,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstSelectState, firstReadState, interveningState, secondSelectState,
    secondReadState, failedState, finalState,
    firstTrace, secondTrace, firstSelectTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondSelectTrace, secondArguments, secondPacking, secondReadTrace,
    failure, failedTrace, failedMeaning, repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed admission makeStages echoStages chooseStages selectStages sequence receiver⟩

end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexSuccessForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
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
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  have rawType : request.header.function.resultType = closureType := by
    rw [selectedHeader]
    exact support.makeHeader.make_result_type
  have applied : RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header request.header
      invocation state.heap [.word value] (.value source) after := by
    simpa only [selectedHeader] using trace
  have forwarded := RecursiveNamedPublicPhysicalSessionExportForward.forward_function_at_input_registry
    support.program fixture.recipePrepared state call.toCall.toStartedCall request inputs rawType ready applied
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, ForwardAt, ReturnedValue,
    closureType] using forwarded


theorem forward_select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    (first second : RecursiveNamedPublicFunctionHistory.Entry)
    (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selectedHeader := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selectedHeader, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have rawType : request.header.function.resultType = closureType := by
    rw [selectedHeader]
    exact support.selectHeader.select_result_type
  have applied : RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header request.header
      invocation state.heap [sourceTable first second, .word key] (.value source) after := by
    simpa only [selectedHeader] using trace
  have forwarded := RecursiveNamedPublicPhysicalSessionExportForward.forward_function_at_input_registry
    support.program fixture.recipePrepared state call.toCall.toStartedCall request inputs rawType ready applied
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, ForwardAt, ReturnedValue,
    closureType] using forwarded


end Tests.SourceCoreRecursiveIndex
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveIndexForward
/-! Every successful step in the checked mapping sequence has independent
Source-to-public bounds at its original start, including the call after failure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def SuccessfulForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.firstSelect
    meaning.firstSelected.source meaning.firstSelectState.heap ∧
  ForwardWordAt meaning.support sequence.firstSelect.completion.session
    [meaning.first, meaning.second, meaning.firstSelected] sequence.firstSelect.handle seed meaning.firstReadState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second, meaning.firstSelected]) meaning.support sequence.intervening
    meaning.intervening.source meaning.interveningState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening])
    meaning.support sequence.secondSelect meaning.secondSelected.source meaning.secondSelectState.heap ∧
  ForwardWordAt meaning.support sequence.secondSelect.completion.session
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]
    sequence.secondSelect.handle secondSeed meaning.secondReadState.heap ∧
  ForwardWordAt meaning.support sequence.failed.returned
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]
    sequence.first.handle seed meaning.finalState.heap

theorem SequenceWitness.successes_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : SuccessfulForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  have failedReady := sequence.failed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_make meaning.initial sequence.second firstReady meaning.secondTrace,
    forward_select meaning.secondState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.firstSelect secondReady meaning.firstSelectTrace,
    forward_word meaning.firstSelectState meaning.firstSelected (by simp)
      meaning.firstSelectedType meaning.firstSelectedHandle meaning.firstSelectedHandleType
      sequence.firstRead firstSelectReady meaning.firstPacking meaning.firstReadTrace,
    forward_make meaning.firstReadState sequence.intervening firstReadReady meaning.interveningTrace,
    forward_select meaning.interveningState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.secondSelect interveningReady meaning.secondSelectTrace,
    forward_word meaning.secondSelectState meaning.secondSelected (by simp)
      meaning.secondSelectedType meaning.secondSelectedHandle meaning.secondSelectedHandleType
      sequence.secondRead secondSelectReady meaning.secondPacking meaning.secondReadTrace,
    forward_word meaning.failedState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType
      sequence.repeatedRead failedReady meaning.repeatedPacking meaning.repeatedReadTrace⟩


def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  SuccessfulForwardMeaning meaning ∧
  ForwardFailureAt meaning.support sequence.failed meaning.failure meaning.failedState.heap
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  exact ⟨meaning.successes_forward,
    forward_failure meaning.secondReadState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.failed secondReadReady meaning.failedTrace⟩

/-- The real accepted program and its observed executions close both directions:
all nine actual steps have Source traces, and each trace implies public progress
at sufficient fuel on the original checkpoint, including the missing-key fault. -/
theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver, ForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ :=
    closed_sequence_meaning fixture observed admission makeStages echoStages chooseStages selectStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  have _automatic := admission.automatic_catalog_initial
  let makeStages ← observeStages fixture observed.makeRow
  let echoStages ← observeStages fixture observed.echoRow
  let chooseStages ← observeStages fixture observed.chooseRow
  let selectStages ← observeStages fixture observed.selectRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed admission makeStages echoStages chooseStages selectStages sequence
  IO.println "Recursive echo(table)[choose(key)]: select A10, allocate30, select B20, missing key, reuse A10; all nine Source traces and public fuel bounds proved"

end Tests.SourceCoreRecursiveIndex
end
