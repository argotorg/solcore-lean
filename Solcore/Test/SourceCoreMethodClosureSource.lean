import Solcore.Test.SourceCoreEvidenceMethodSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode
abbrev TraitShape := Tests.SourceCoreEvidenceMethod.TraitShape
abbrev observeTrait := Tests.SourceCoreEvidenceMethod.observeTrait
abbrev ImplementationShape := Tests.SourceCoreEvidenceMethod.ImplementationShape
abbrev observeImplementation := Tests.SourceCoreEvidenceMethod.observeImplementation
def predicate (trait : ProgramTraitId) (type : TypeSystem.Ty) : ProgramPredicate := ⟨trait, type, []⟩
def closureType (type : TypeSystem.Ty) : TypeSystem.Ty := .function .unit type
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

structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) (argument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function type (closureType type))
  value : CallNode source (closureType type)
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)],
    .function (.parameter parameter) (closureType (.parameter parameter))⟩
  inputs : signature.parameterTypes = [.parameter parameter]
  returns : signature.returnTypes = [closureType (.parameter parameter)]
  exact : instantiation = ⟨signature.id, [(parameter, type)],
    .function type (closureType type), [predicate trait type], signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source signature parameter type argument trait}
    (call : DirectCall source signature parameter type argument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context type)
    (typed : ExpressionHasType source context argument type)
    (required : RequirementProves context call.requirement (predicate trait type)) :
    ExpressionHasType source context call.value.node.id (closureType type) := by
  have resultFormed : TypeAdmissible context (closureType type) :=
    ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin
      (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · constructor
      · simp [call.scheme]
      · simp [ParameterSubstitution.domain, call.scheme]
    · intro parameter replacement contained
      cases List.mem_singleton.mp contained
      exact firstFormed
    · simp [call.scheme, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, closureType]
    · simp [call.scheme, predicate, ProgramPredicate.applyParameters, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, closureType]
  have application : DeclarationApplicationValid context call.instantiation [type] (closureType type) [predicate trait type] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, closureType]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, closureType]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons typed (.nil _)))
      call.value.raw resultFormed (call.value.type.symm ▸ resultFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty)
    (argument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (DirectCall source signature parameter type argument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function type (closureType type))
  let value ← observeCallNode source value (closureType type)
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.declaration instantiation)) "generic direct form"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)], .function (.parameter parameter) (closureType (.parameter parameter))⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter parameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType (.parameter parameter)]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(parameter, type)], .function type (closureType type), [predicate trait type], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}


structure ReturnShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (inputType type : TypeSystem.Ty) (expression : ExpressionId) where
  binder : TypedBinder
  read : Read function.typedBody binder inputType
  statement : StatementNode
  inputs : function.typedBody.inputs = [binder]
  inputTypes : signature.parameterTypes = [inputType]
  returns : signature.returnTypes = [type]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some expression)
  statementType : statement.type = type

theorem ReturnShape.statementTyping {function signature inputType type expression}
    (shape : ReturnShape function signature inputType type expression) (signatures : ProgramSignatures)
    (typed : ∀ lexical, MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
      function.typedBody.inputs signature.parameterTypes lexical →
      ExpressionHasType function.typedBody lexical expression type) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := type, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
    shape.statementForm (typed lexical extension) shape.statementType)⟩

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) where
  expression : ExpressionId
  body : ReturnShape function signature type (closureType type) expression
  call : DirectCall function.typedBody generic parameter type body.read.node.id trait
  result : expression = call.value.node.id
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = predicate trait type
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []

def RootShape.nodeList {function signature generic parameter type trait}
    (shape : RootShape function signature generic parameter type trait) : List Node :=
  [.expression shape.body.read.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.body.statement]

theorem RootShape.statementTyping {function signature generic parameter type trait}
    (shape : RootShape function signature generic parameter type trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody) :
    CheckedBodyStatementsHaveType signatures signature function := by
  apply shape.body.statementTyping signatures
  intro lexical extension
  rw [shape.body.inputs, shape.body.inputTypes] at extension
  cases extension with
  | cons scheme head rest =>
    cases rest
    have fields : lexical.signatures = signatures := head.context_fields.1
    have types := StructuralSubstitution.TypesWellFormed.transportContext
      head.context_fields.1 head.context_fields.2.2.1 head.context_fields.2.1 header.parameter_types
    have formed := TypeAdmissible.ofWellFormed (types type (by simp [shape.body.inputTypes]))
    have currentLedger := ledger.transportContext head.context_fields.1
      head.context_fields.2.2.2.1 head.context_fields.2.2.2.2
    have rowMember : shape.solved ∈ lexical.solvedRequirements := by
      rw [head.context_fields.2.2.2.2]
      exact shape.solvedMember
    have required : RequirementProves lexical shape.call.requirement (predicate trait type) :=
      ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
        currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
    rw [shape.result]
    exact shape.call.typed (fields ▸ member) formed
      (shape.body.read.typed scheme shape.body.binderRequirements formed head.local_self head.local_scheme_requirements_self)
      required

def observeReturn (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (inputType type : TypeSystem.Ty) (expression : ExpressionId) (readNode : ExpressionNode) (statement : StatementNode) :
    IO (ReturnShape function signature inputType type expression) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "method fixture input count")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode inputType
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "return inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [inputType]) "return signature inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [type]) "return signature result"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "return binder requirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "return roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "return lookup"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some expression)) "return form"
  let ⟨statementType⟩ ← observed (statement.type = type) "return type"
  return {binder := binder, read, statement, inputs, inputTypes, returns, binderRequirements, roots, statementFound, statementForm, statementType}

def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RootShape function signature generic parameter type trait) := do
  let [.expression readNode, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let body ← observeReturn function signature type (closureType type) value.id readNode statement
  let call ← observeDirect function.typedBody generic parameter type body.read.node.id callee value trait
  let ⟨result⟩ ← observed (value.id = call.value.node.id) "root result identity"
  match rows : function.solvedRequirements with
  | [solved] =>
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "root solved requirement"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait type) "root solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "root templates"
    return {expression := value.id, body, call, result, solved, solvedMember := by simp [rows], solvedId, solvedPredicate, noTemplates}
  | _ => throw (IO.userError "root requirement ledger")


structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (trait : ProgramTraitId) where
  expression : TypedNode function.typedBody (closureType (.parameter parameter))
  value : CallNode function.typedBody (.parameter parameter)
  body : ReturnShape function signature (.parameter parameter) (closureType (.parameter parameter)) expression.node.id
  statement : StatementNode
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some value.node.id)
  statementType : statement.type = .parameter parameter
  lambda : expression.node.form = .lambda [] (.parameter parameter) [statement.id]
  form : value.node.form = .unary .bitNot body.read.node.id
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = requirement
  solvedPredicate : solved.predicate = predicate trait (.parameter parameter)
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []

def FactoryShape.nodeList {function signature parameter trait}
    (shape : FactoryShape function signature parameter trait) : List Node :=
  [.expression shape.body.read.node, .expression shape.value.node, .statement shape.statement,
   .expression shape.expression.node, .statement shape.body.statement]

theorem FactoryShape.statementTyping {function signature parameter trait}
    (shape : FactoryShape function signature parameter (.declaration trait.id))
    (catalog : TraitShape trait) (signatures : ProgramSignatures) (member : trait ∈ signatures.traits)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody) :
    CheckedBodyStatementsHaveType signatures signature function := by
  apply shape.body.statementTyping signatures
  intro lexical extension
  rw [shape.body.inputs, shape.body.inputTypes] at extension
  cases extension with
  | cons scheme head rest =>
    cases rest
    have fields : lexical.signatures = signatures := head.context_fields.1
    have types := StructuralSubstitution.TypesWellFormed.transportContext
      head.context_fields.1 head.context_fields.2.2.1 head.context_fields.2.1 header.parameter_types
    have formed := TypeAdmissible.ofWellFormed (types (.parameter parameter) (by simp [shape.body.inputTypes]))
    have currentLedger := ledger.transportContext head.context_fields.1
      head.context_fields.2.2.2.1 head.context_fields.2.2.2.2
    have rowMember : shape.solved ∈ lexical.solvedRequirements := by
      rw [head.context_fields.2.2.2.2]
      exact shape.solvedMember
    have required : RequirementProves lexical shape.requirement (predicate (.declaration trait.id) (.parameter parameter)) :=
      ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
        currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
    have profile : UnaryOperatorHasType lexical .bitNot (.parameter parameter) (.parameter parameter) [shape.requirement] :=
      .trait .bitNot (catalog.profile (fields ▸ member) (.parameter parameter)) (.cons required .nil)
    have typed : ExpressionHasType function.typedBody lexical shape.value.node.id shape.value.node.type := by
      refine .intro (lookupExpression?_sound shape.value.found)
        (shape.form ▸ ExpressionFormHasRawType.unary
          (shape.body.read.typed scheme shape.body.binderRequirements formed head.local_self head.local_scheme_requirements_self) profile)
        shape.value.raw formed (shape.value.type.symm ▸ formed) ?_
      rw [shape.requirements, shape.value.coercions, shape.value.type]
      exact .ordinary profile.requirements_valid (.nil _) rfl
    have resultTyped : ExpressionHasType function.typedBody lexical shape.value.node.id (.parameter parameter) :=
      Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.value.node.id type) shape.value.type) typed
    have callable : TypeAdmissible lexical (closureType (.parameter parameter)) :=
      ⟨formed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin
        (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) formed)⟩
    exact shape.expression.ordinary callable
      (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
        (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
          shape.statementForm resultTyped shape.statementType))
        (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩))

def observeFactory (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (trait : ProgramTraitId) :
    IO (FactoryShape function signature parameter trait) := do
  let [.expression readNode, .expression node, .statement statement, .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "factory original five nodes")
  let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType (.parameter parameter))
  let value ← observeCallNode function.typedBody node (.parameter parameter)
  let body ← observeReturn function signature (.parameter parameter) (closureType (.parameter parameter)) expression.node.id readNode outerReturn
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "factory inner statement lookup"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some value.node.id)) "factory inner return"
  let ⟨statementType⟩ ← observed (statement.type = .parameter parameter) "factory inner return type"
  let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] (.parameter parameter) [statement.id]) "factory lambda"
  let [requirement] := node.requirements | throw (IO.userError "operator requirement count")
  let ⟨form⟩ ← observed (value.node.form = .unary .bitNot body.read.node.id) "operator form"
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "operator requirements"
  match rows : function.solvedRequirements with
  | [solved] =>
    let ⟨solvedId⟩ ← observed (solved.id = requirement) "operator solved requirement"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait (.parameter parameter)) "operator solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "operator templates"
    return {expression := expression, value := value, body := body, statement := statement,
            statementFound := statementFound, statementForm := statementForm, statementType := statementType,
            lambda := lambda, form := form, requirement := requirement, requirements := requirements,
            solved := solved, solvedMember := by simp [rows], solvedId := solvedId,
            solvedPredicate := solvedPredicate, noTemplates := noTemplates}
  | _ => throw (IO.userError "operator requirement ledger")

structure UseShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) where
  value : TypedNode function.typedBody type
  body : ReturnShape function signature (closureType type) type value.node.id
  metadata : IndirectCallResolution
  form : value.node.form = .call body.read.node.id [] (.indirect metadata)
  application : metadata = ⟨0, .unit, .unit, []⟩

def UseShape.nodeList {function signature type}
    (shape : UseShape function signature type) : List Node :=
  [.expression shape.body.read.node, .expression shape.value.node, .statement shape.body.statement]

theorem UseShape.statementTyping {function signature type}
    (shape : UseShape function signature type) (signatures : ProgramSignatures)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (admissible : ∀ context, TypeParameterBindersWellFormed context → TypeAdmissible context type) :
    CheckedBodyStatementsHaveType signatures signature function := by
  apply shape.body.statementTyping signatures
  intro lexical extension
  rw [shape.body.inputs, shape.body.inputTypes] at extension
  cases extension with
  | cons scheme head rest =>
    cases rest
    have types := StructuralSubstitution.TypesWellFormed.transportContext
      head.context_fields.1 head.context_fields.2.2.1 head.context_fields.2.1 header.parameter_types
    have callable := TypeAdmissible.ofWellFormed (types (closureType type) (by simp [shape.body.inputTypes]))
    have formed := admissible lexical callable.1
    have readTyped := shape.body.read.typed scheme shape.body.binderRequirements callable
      head.local_self head.local_scheme_requirements_self
    have application : IndirectApplicationValid lexical shape.metadata [] .unit := by
      rw [shape.application]
      exact .intro rfl rfl rfl (.nil _)
    have typed : ExpressionHasType function.typedBody lexical shape.value.node.id shape.value.node.type := by
      refine .intro (lookupExpression?_sound shape.value.found)
        (shape.form ▸ ExpressionFormHasRawType.indirectCall readTyped (.nil _) application)
        shape.value.raw formed (shape.value.type.symm ▸ formed) ?_
      rw [shape.value.requirements, shape.value.coercions, shape.value.type, shape.application]
      exact .indirectCall (by intro id member; cases member) (.nil _) rfl
    exact Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.value.node.id type) shape.value.type) typed

def observeUse (function : CheckedFunction) (signature : ProgramFunctionSignature) (type : TypeSystem.Ty) :
    IO (UseShape function signature type) := do
  let [.expression readNode, .expression node, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "use original three nodes")
  let value ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody node type
  let body ← observeReturn function signature (closureType type) type value.node.id readNode statement
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "use indirect call")
  let ⟨form⟩ ← observed (value.node.form = .call body.read.node.id [] (.indirect metadata)) "use indirect form"
  let ⟨application⟩ ← observed (metadata = ⟨0, .unit, .unit, []⟩) "use indirect metadata"
  return {value, body, metadata, form, application}

def content : String := String.intercalate "\n" [
  "trait BitNot<T> { function bnot(value: T) returns (T); }",
  "impl BitNot<Word> { function bnot(value: Word) returns (Word) { return value; } }",
  "impl BitNot<Bool> { function bnot(value: Bool) returns (Bool) { return value; } }",
  "function make<T>(value: T) returns (function() returns (T)) where T: BitNot { return lam() -> T { return ~value; }; }",
  "function wordRoot(value: Word) returns (function() returns (Word)) { return make(value); }",
  "function boolRoot(value: Bool) returns (function() returns (Bool)) { return make(value); }",
  "function useWord(f: function() returns (Word)) returns (Word) { return f(); }",
  "function useBool(f: function() returns (Bool)) returns (Bool) { return f(); }"]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] }

/-- Original checked declarations and their independent Source statement typing.
Method bodies retain genuine implementation signatures. -/
structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1024 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitSignature
  traitShape : TraitShape trait
  traits : program.signatures.traits = [trait]
  parameter : TypeSystem.TypeParameterId
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  wordFunction : CheckedFunction
  wordSignature : ProgramFunctionSignature
  boolFunction : CheckedFunction
  boolSignature : ProgramFunctionSignature
  useWordFunction : CheckedFunction
  useWordSignature : ProgramFunctionSignature
  useBoolFunction : CheckedFunction
  useBoolSignature : ProgramFunctionSignature
  functions : program.functions = [makeFunction, wordFunction, boolFunction, useWordFunction, useBoolFunction]
  signatures : program.signatures.functions = [makeSignature, wordSignature, boolSignature, useWordSignature, useBoolSignature]
  methodCount : program.methods.length = 2
  wordImplementation : ProgramImplementationSignature
  boolImplementation : ProgramImplementationSignature
  implementations : program.signatures.implementations = [wordImplementation, boolImplementation]
  wordMethod : ImplementationShape program wordImplementation .word
  boolMethod : ImplementationShape program boolImplementation .bool
  makeDeclaration : makeFunction.declaration = makeSignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  useWordDeclaration : useWordFunction.declaration = useWordSignature.id
  useBoolDeclaration : useBoolFunction.declaration = useBoolSignature.id
  makeShape : FactoryShape makeFunction makeSignature parameter (.declaration trait.id)
  wordShape : RootShape wordFunction wordSignature makeSignature parameter .word (.declaration trait.id)
  boolShape : RootShape boolFunction boolSignature makeSignature parameter .bool (.declaration trait.id)
  useWordShape : UseShape useWordFunction useWordSignature .word
  useBoolShape : UseShape useBoolFunction useBoolSignature .bool
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList
  useWordNodes : useWordFunction.typedBody.nodes = useWordShape.nodeList
  useBoolNodes : useBoolFunction.typedBody.nodes = useBoolShape.nodeList

private theorem checkedHeader {program : CheckedProgram} (checked : checkProgram workspace 1024 = .ok program)
    {function signature} (member : function ∈ program.functions) (signatureMember : signature ∈ program.signatures.functions)
    (accepted : checkFunctionBody program.environment program.signatures signature 1024 = .ok function) :
    CheckedBodyHeaderWellFormed program.signatures signature function := by
  obtain ⟨other, otherMember, header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked member
  have same : other = signature := eq_of_mem_of_nodup_map
    (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids otherMember signatureMember
    (header.declaration_eq.symm.trans (checkFunctionBody_success_declaration accepted))
  exact same ▸ header

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1024 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions,
        traits : program.signatures.traits, implementations : program.signatures.implementations with
    | [makeFunction, wordFunction, boolFunction, useWordFunction, useBoolFunction],
        [makeSignature, wordSignature, boolSignature, useWordSignature, useBoolSignature],
        [trait], [wordImplementation, boolImplementation] =>
      let traitShape ← observeTrait trait
      let [parameter] := makeSignature.scheme.parameters | throw (IO.userError "make generic parameter")
      let makeShape ← observeFactory makeFunction makeSignature parameter (.declaration trait.id)
      let wordShape ← observeRoot wordFunction wordSignature makeSignature parameter .word (.declaration trait.id)
      let boolShape ← observeRoot boolFunction boolSignature makeSignature parameter .bool (.declaration trait.id)
      let useWordShape ← observeUse useWordFunction useWordSignature .word
      let useBoolShape ← observeUse useBoolFunction useBoolSignature .bool
      let wordMethod ← observeImplementation program wordImplementation .word
      let boolMethod ← observeImplementation program boolImplementation .bool
      let ⟨methodCount⟩ ← observed (program.methods.length = 2) "original method inventory"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
      let ⟨useWordDeclaration⟩ ← observed (useWordFunction.declaration = useWordSignature.id) "useWord declaration"
      let ⟨useBoolDeclaration⟩ ← observed (useBoolFunction.declaration = useBoolSignature.id) "useBool declaration"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "word nodes"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "bool nodes"
      let ⟨useWordNodes⟩ ← observed (useWordFunction.typedBody.nodes = useWordShape.nodeList) "useWord nodes"
      let ⟨useBoolNodes⟩ ← observed (useBoolFunction.typedBody.nodes = useBoolShape.nodeList) "useBool nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1024 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          have header := checkedHeader checked member candidateMember accepted
          have ledger := SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
            (checkProgram_success_signature_formation checked) candidateMember accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl
          · have same : candidate = makeSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans makeDeclaration)
            subst candidate
            exact makeShape.statementTyping traitShape program.signatures (by simp [traits]) header ledger
          · have same : candidate = wordSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans wordDeclaration)
            subst candidate
            exact wordShape.statementTyping program.signatures (by simp [signatures]) header ledger
          · have same : candidate = boolSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans boolDeclaration)
            subst candidate
            exact boolShape.statementTyping program.signatures (by simp [signatures]) header ledger
          · have same : candidate = useWordSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans useWordDeclaration)
            subst candidate
            exact useWordShape.statementTyping program.signatures header (fun _ binders => ⟨binders, .builtin .word⟩)
          · have same : candidate = useBoolSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans useBoolDeclaration)
            subst candidate
            exact useBoolShape.statementTyping program.signatures header (fun _ binders => ⟨binders, .builtin .bool⟩)
        methods := by
          intro actual _member implementation method trait member methodMember lookup accepted
          simp only [implementations, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact wordMethod.statementTyping (fun _ binders => ⟨binders, .builtin .word⟩) methodMember lookup accepted
          · exact boolMethod.statementTyping (fun _ binders => ⟨binders, .builtin .bool⟩) methodMember lookup accepted }
      return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep,
              program, checked, trait, traitShape, traits, parameter,
              makeFunction, makeSignature, wordFunction, wordSignature, boolFunction, boolSignature, useWordFunction, useWordSignature, useBoolFunction, useBoolSignature,
              functions, signatures, methodCount, wordImplementation, boolImplementation, implementations, wordMethod, boolMethod,
              makeDeclaration, wordDeclaration, boolDeclaration, useWordDeclaration, useBoolDeclaration,
              makeShape, wordShape, boolShape, useWordShape, useBoolShape,
              makeNodes, wordNodes, boolNodes, useWordNodes, useBoolNodes}
    | _, _, _, _ => throw (IO.userError "method closure original declaration inventory")

end Tests.SourceCoreMethodClosure
