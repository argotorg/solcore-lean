import Solcore.Test.SourceCoreOperatorCallsSource
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreBuiltinCalls
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
    "function identity(value: Word) returns (Word) { return value; } function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function relay(seed: Word) returns (function() returns (Word)) { return make(identity(seed) + wordFromInteger(0)); }"}] }

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

private theorem builtin_integer_evidence (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .integer)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .integer) (.builtin .intInteger) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntIntegerRule) (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

structure IntegerLiteral (function : CheckedFunction) where
  node : ExpressionNode
  spelling : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  validated : SourceCoreElaboration.NativeIntegerLiteral
  found : function.typedBody.lookupExpression? node.id = some node
  form : node.form = .integerLiteral spelling resolution
  raw : node.rawType = .integer
  accepted : SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node spelling resolution = .ok validated

theorem IntegerLiteral.typed {function : CheckedFunction} (literal : IntegerLiteral function)
    {context : SourceSemantics.Context} (word : TypeAdmissible context .integer)
    (ledger : context.solvedRequirements = function.solvedRequirements) :
    ExpressionHasType function.typedBody context literal.node.id .integer := by
  have metadata := SourceCoreElaboration.validateNativeIntegerLiteral_sound literal.accepted
  obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.integer literal.accepted
  have member : row ∈ function.solvedRequirements.filter (fun row => decide (row.id = literal.resolution.requirement)) := by
    rw [selected]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have proves : RequirementProves context literal.resolution.requirement
      (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) := by
    refine ⟨row, ⟨ledger ▸ member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
    rw [evidence, predicate]
    change RetainedEvidenceValid _ _ (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) _
    rw [metadata.targetType]
    simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_integer_evidence context
  have valid : IntegerLiteralValid context literal.spelling literal.resolution :=
    .integer metadata.meaning metadata.targetType proves
  have typed : ExpressionHasType function.typedBody context literal.node.id literal.node.type := by
    refine .intro (lookupExpression?_sound literal.found)
      (literal.form ▸ ExpressionFormHasRawType.integerLiteral valid)
      (literal.raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ word)
      (metadata.nodeType.symm ▸ word) ?_
    rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
    exact .ordinary (by intro id member; have same := List.mem_singleton.mp member; exact same ▸ valid.requirement_valid) (.nil _) rfl
  exact metadata.nodeType ▸ typed

/-- Actual compiler-provided builtin callee and ordered argument metadata. -/
structure BuiltinCall (source : TypedSource) (function : BuiltinFunctionId)
    (argument : ExpressionId) where
  callee : TypedNode source function.type
  value : TypedNode source function.returnType
  name : String
  calleeForm : callee.node.form = .reference name (.builtinFunction function)
  form : value.node.form = .call callee.node.id [argument] (.builtinFunction function)

theorem BuiltinCall.typed {source : TypedSource} {function : BuiltinFunctionId}
    {argument : ExpressionId} (call : BuiltinCall source function argument)
    {context : SourceSemantics.Context} {parameter : TypeSystem.Ty}
    (parameters : function.parameterTypes = [parameter])
    (admissible : TypeAdmissible context function.returnType)
    (argumentTyped : ExpressionHasType source context argument parameter) :
    ExpressionHasType source context call.value.node.id function.returnType := by
  have callee : DirectBuiltinCalleeValid source call.callee.node.id function :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm
      call.callee.type call.callee.requirements call.callee.coercions
  have arguments : ExpressionsHaveTypes source context [argument] function.parameterTypes := by
    rw [parameters]
    exact .cons argumentTyped (.nil _)
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.builtinCall callee arguments)
      call.value.raw admissible (call.value.type.symm ▸ admissible) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

private def observeBuiltin (source : TypedSource) (function : BuiltinFunctionId)
    (argument : ExpressionId) (calleeNode valueNode : ExpressionNode) :
    IO (BuiltinCall source function argument) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source calleeNode function.type
  let value ← Tests.SourceCoreOperatorCalls.observeNode source valueNode function.returnType
  let .reference name (.builtinFunction _) := calleeNode.form
    | throw (IO.userError "builtin callee original form")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.builtinFunction function)) "builtin callee metadata"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.builtinFunction function)) "builtin call metadata"
  return {callee, value, name, calleeForm, form}

structure RelayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  inner : DirectCall function.typedBody identity read.node.id .word
  zero : IntegerLiteral function
  converted : BuiltinCall function.typedBody .wordFromInteger zero.node.id
  sum : TypedNode function.typedBody .word
  sumForm : sum.node.form = .binary inner.value.node.id .add converted.value.node.id
  outer : DirectCall function.typedBody maker sum.node.id closureType
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
   .expression shape.zero.node, .expression shape.converted.callee.node,
   .expression shape.converted.value.node, .expression shape.sum.node,
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
    have integer : TypeAdmissible lexical .integer := ⟨binders, .builtin .integer⟩
    have ledger : lexical.solvedRequirements = function.solvedRequirements := by cases head; rfl
    have zero := shape.zero.typed integer ledger
    have converted := shape.converted.typed rfl word zero
    have sum := shape.sum.ordinary word (shape.sumForm ▸ .binary inner converted (.wordArithmetic .add))
    have outer := shape.outer.typed (fields ▸ makeMember) callable sum
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

def observeIntegerLiteral (function : CheckedFunction) (node : ExpressionNode) : IO (IntegerLiteral function) := do
  match form : node.form with
  | .integerLiteral spelling resolution =>
    match accepted : SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node spelling resolution with
    | .error error => throw (IO.userError (reprStr error))
    | .ok validated =>
      let ⟨found⟩ ← observed (function.typedBody.lookupExpression? node.id = some node) "literal lookup"
      let ⟨raw⟩ ← observed (node.rawType = .integer) "literal raw Integer"
      return ⟨node, spelling, resolution, validated, found, form, raw, accepted⟩
  | _ => throw (IO.userError "integer literal expected")

def relayShape (function : CheckedFunction) (signature identity maker : ProgramFunctionSignature) :
    IO (RelayShape function signature identity maker) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay input")
  let [.expression read, .expression innerCallee, .expression innerValue,
      .expression zeroNode, .expression convertedCallee,
      .expression convertedValue, .expression sumNode,
      .expression outerCallee, .expression outerValue, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "relay original nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .word
  let inner ← observeDirect function.typedBody identity read.node.id innerCallee innerValue .word
  let zero ← observeIntegerLiteral function zeroNode
  let converted ← observeBuiltin function.typedBody .wordFromInteger zero.node.id convertedCallee convertedValue
  let sum ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody sumNode .word
  let ⟨sumForm⟩ ← observed (sum.node.form = .binary inner.value.node.id .add converted.value.node.id) "relay sum form"
  let outer ← observeDirect function.typedBody maker sum.node.id outerCallee outerValue closureType
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
  return {binder, read, inner, zero, converted, sum, sumForm, outer, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, roots, statementFound, statementForm, statementType}

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

end Tests.SourceCoreBuiltinCalls
