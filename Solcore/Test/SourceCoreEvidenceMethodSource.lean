import Solcore.Test.SourceCoreEvidenceDirectSource
import Solcore.Test.SourceCoreRecursiveIndexSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode
def predicate (trait : ProgramTraitId) (type : TypeSystem.Ty) : ProgramPredicate := ⟨trait, type, []⟩
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
  callee : TypedNode source (.function type type)
  value : CallNode source type
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)],
    .function (.parameter parameter) (.parameter parameter)⟩
  inputs : signature.parameterTypes = [.parameter parameter]
  returns : signature.returnTypes = [.parameter parameter]
  exact : instantiation = ⟨signature.id, [(parameter, type)],
    .function type type, [predicate trait type], signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source signature parameter type argument trait}
    (call : DirectCall source signature parameter type argument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context type)
    (typed : ExpressionHasType source context argument type)
    (required : RequirementProves context call.requirement (predicate trait type)) :
    ExpressionHasType source context call.value.node.id type := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · constructor
      · simp [call.scheme]
      · simp [ParameterSubstitution.domain, call.scheme]
    · intro parameter replacement contained
      cases List.mem_singleton.mp contained
      exact firstFormed
    · simp [call.scheme, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
    · simp [call.scheme, predicate, ProgramPredicate.applyParameters, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
  have application : DeclarationApplicationValid context call.instantiation [type] type [predicate trait type] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons typed (.nil _)))
      call.value.raw firstFormed (call.value.type.symm ▸ firstFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty)
    (argument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (DirectCall source signature parameter type argument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function type type)
  let value ← observeCallNode source value type
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [argument] (.declaration instantiation)) "generic direct form"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)], .function (.parameter parameter) (.parameter parameter)⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter parameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter parameter]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(parameter, type)], .function type type, [predicate trait type], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}


structure ReturnShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (expression : ExpressionId) where
  binder : TypedBinder
  read : Read function.typedBody binder type
  statement : StatementNode
  inputs : function.typedBody.inputs = [binder]
  inputTypes : signature.parameterTypes = [type]
  returns : signature.returnTypes = [type]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some expression)
  statementType : statement.type = type

theorem ReturnShape.statementTyping {function signature type expression}
    (shape : ReturnShape function signature type expression) (signatures : ProgramSignatures)
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
  body : ReturnShape function signature type expression
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

structure TraitShape (trait : ProgramTraitSignature) where
  parameter : TypeSystem.TypeParameterId
  method : ProgramTraitMethodSignature
  name : trait.name = "BitNot"
  parameters : trait.parameters = [parameter]
  unique : trait.methods.filter (fun method => method.name == "bnot") = [method]
  inputs : method.parameterTypes = [.parameter parameter]
  returns : method.returnTypes = [.parameter parameter]
  predicates : method.wherePredicates = []

theorem TraitShape.profile {trait : ProgramTraitSignature} (shape : TraitShape trait)
    {context : SourceSemantics.Context} (member : trait ∈ context.signatures.traits) (type : TypeSystem.Ty) :
    OperatorProfileInstantiates context "BitNot" "bnot" type [type] [type]
      [predicate (.declaration trait.id) type] := by
  have profile := OperatorProfileInstantiates.intro (operand := type) (parameterTypes := [type]) (returnTypes := [type]) member shape.name shape.parameters shape.unique
    (by simp [shape.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?])
    (by simp [shape.returns, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?])
  simpa only [shape.predicates, List.map_nil, predicate] using profile

structure ViaShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (trait : ProgramTraitId) where
  value : CallNode function.typedBody (.parameter parameter)
  body : ReturnShape function signature (.parameter parameter) value.node.id
  form : value.node.form = .unary .bitNot body.read.node.id
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = requirement
  solvedPredicate : solved.predicate = predicate trait (.parameter parameter)
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []

def ViaShape.nodeList {function signature parameter trait}
    (shape : ViaShape function signature parameter trait) : List Node :=
  [.expression shape.body.read.node, .expression shape.value.node, .statement shape.body.statement]

theorem ViaShape.statementTyping {function signature parameter trait}
    (shape : ViaShape function signature parameter (.declaration trait.id))
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
    exact Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.value.node.id type) shape.value.type) typed

def observeReturn (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (expression : ExpressionId) (readNode : ExpressionNode) (statement : StatementNode) :
    IO (ReturnShape function signature type expression) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "method fixture input count")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode type
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "return inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type]) "return signature inputs"
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
  let body ← observeReturn function signature type value.id readNode statement
  let call ← observeDirect function.typedBody generic parameter type body.read.node.id callee value trait
  let ⟨result⟩ ← observed (value.id = call.value.node.id) "root result identity"
  match rows : function.solvedRequirements with
  | [solved] =>
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "root solved requirement"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait type) "root solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "root templates"
    return {expression := value.id, body, call, result, solved, solvedMember := by simp [rows], solvedId, solvedPredicate, noTemplates}
  | _ => throw (IO.userError "root requirement ledger")

def observeTrait (trait : ProgramTraitSignature) : IO (TraitShape trait) := do
  let [parameter] := trait.parameters | throw (IO.userError "operator trait parameters")
  let ⟨name⟩ ← observed (trait.name = "BitNot") "operator trait name"
  let ⟨parameters⟩ ← observed (trait.parameters = [parameter]) "operator trait parameter"
  match rows : trait.methods with
  | [method] =>
    let ⟨methodName⟩ ← observed (method.name = "bnot") "operator method name"
    let ⟨inputs⟩ ← observed (method.parameterTypes = [.parameter parameter]) "operator method input"
    let ⟨returns⟩ ← observed (method.returnTypes = [.parameter parameter]) "operator method result"
    let ⟨predicates⟩ ← observed (method.wherePredicates = []) "operator method predicates"
    return {parameter, method, name, parameters, unique := by simp [rows, methodName], inputs, returns, predicates}
  | _ => throw (IO.userError "operator trait methods")

def observeVia (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (trait : ProgramTraitId) :
    IO (ViaShape function signature parameter trait) := do
  let [.expression readNode, .expression node, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "operator body nodes")
  let value ← observeCallNode function.typedBody node (.parameter parameter)
  let body ← observeReturn function signature (.parameter parameter) value.node.id readNode statement
  let [requirement] := node.requirements | throw (IO.userError "operator requirement count")
  let ⟨form⟩ ← observed (value.node.form = .unary .bitNot body.read.node.id) "operator form"
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "operator requirements"
  match rows : function.solvedRequirements with
  | [solved] =>
    let ⟨solvedId⟩ ← observed (solved.id = requirement) "operator solved requirement"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait (.parameter parameter)) "operator solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "operator templates"
    return {value, body, form, requirement, requirements, solved, solvedMember := by simp [rows], solvedId, solvedPredicate, noTemplates}
  | _ => throw (IO.userError "operator requirement ledger")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait BitNot<T> { function bnot(value: T) returns (T); }",
    "impl BitNot<Word> { function bnot(value: Word) returns (Word) { return value; } }",
    "impl BitNot<Bool> { function bnot(value: Bool) returns (Bool) { return value; } }",
    "function via<T>(value: T) returns (T) where T: BitNot { return ~value; }",
    "function wordRoot(value: Word) returns (Word) { return via(value); }",
    "function boolRoot(value: Bool) returns (Bool) { return via(value); }"]}] }

/-- Every implementation body is checked at its genuine method signature.
The resulting independent body typing applies to any matching checker output. -/
structure ImplementationShape (program : CheckedProgram) (implementation : ProgramImplementationSignature)
    (type : TypeSystem.Ty) where
  method : ProgramImplMethodSignature
  trait : ProgramTraitSignature
  function : CheckedFunction
  methods : implementation.methods = [method]
  traitLookup : program.signatures.trait? method.traitMethod.trait = some trait
  checked : checkFunctionBody program.environment program.signatures
    (implementation.functionSignatureOfMethodWithTrait trait method) 1024 = .ok function
  shape : Tests.SourceCoreRecursiveIndex.IdentityShape function
    (implementation.functionSignatureOfMethodWithTrait trait method) type

theorem ImplementationShape.statementTyping {program implementation type}
    (given : ImplementationShape program implementation type)
    (admissible : ∀ context, TypeParameterBindersWellFormed context → TypeAdmissible context type)
    {method trait function}
    (member : method ∈ implementation.methods)
    (lookup : program.signatures.trait? method.traitMethod.trait = some trait)
    (checked : checkFunctionBody program.environment program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) 1024 = .ok function) :
    CheckedBodyStatementsHaveType program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) function := by
  rw [given.methods] at member
  cases List.mem_singleton.mp member
  have sameTrait := Option.some.inj (lookup.symm.trans given.traitLookup)
  subst trait
  have sameFunction := Except.ok.inj (checked.symm.trans given.checked)
  subst function
  exact given.shape.statementTyping program.signatures admissible

def observeImplementation (program : CheckedProgram) (implementation : ProgramImplementationSignature)
    (type : TypeSystem.Ty) : IO (ImplementationShape program implementation type) := do
  match methods : implementation.methods with
  | [method] =>
    match traitLookup : program.signatures.trait? method.traitMethod.trait with
    | none => throw (IO.userError "method trait missing")
    | some trait =>
      match checked : checkFunctionBody program.environment program.signatures
          (implementation.functionSignatureOfMethodWithTrait trait method) 1024 with
      | .error error => throw (IO.userError (reprStr error))
      | .ok function =>
        let shape ← Tests.SourceCoreRecursiveIndex.observeIdentity function
          (implementation.functionSignatureOfMethodWithTrait trait method) type
        return {method, trait, function, methods, traitLookup, checked, shape}
  | _ => throw (IO.userError "implementation method count")

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1024 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitSignature
  traitShape : TraitShape trait
  traits : program.signatures.traits = [trait]
  parameter : TypeSystem.TypeParameterId
  viaFunction : CheckedFunction
  viaSignature : ProgramFunctionSignature
  wordFunction : CheckedFunction
  wordSignature : ProgramFunctionSignature
  boolFunction : CheckedFunction
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [viaFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [viaSignature, wordSignature, boolSignature]
  methodCount : program.methods.length = 2
  wordImplementation : ProgramImplementationSignature
  boolImplementation : ProgramImplementationSignature
  implementations : program.signatures.implementations = [wordImplementation, boolImplementation]
  wordMethod : ImplementationShape program wordImplementation .word
  boolMethod : ImplementationShape program boolImplementation .bool
  viaDeclaration : viaFunction.declaration = viaSignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  viaWord : viaSignature.id ≠ wordSignature.id
  viaBool : viaSignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  viaShape : ViaShape viaFunction viaSignature parameter (.declaration trait.id)
  wordShape : RootShape wordFunction wordSignature viaSignature parameter .word (.declaration trait.id)
  boolShape : RootShape boolFunction boolSignature viaSignature parameter .bool (.declaration trait.id)
  viaNodes : viaFunction.typedBody.nodes = viaShape.nodeList
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList

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
    | [viaFunction, wordFunction, boolFunction], [viaSignature, wordSignature, boolSignature], [trait], [wordImplementation, boolImplementation] =>
      let traitShape ← observeTrait trait
      let [parameter] := viaSignature.scheme.parameters | throw (IO.userError "via generic parameter")
      let viaShape ← observeVia viaFunction viaSignature parameter (.declaration trait.id)
      let wordShape ← observeRoot wordFunction wordSignature viaSignature parameter .word (.declaration trait.id)
      let boolShape ← observeRoot boolFunction boolSignature viaSignature parameter .bool (.declaration trait.id)
      let wordMethod ← observeImplementation program wordImplementation .word
      let boolMethod ← observeImplementation program boolImplementation .bool
      let ⟨methodCount⟩ ← observed (program.methods.length = 2) "original nonempty method inventory"
      let ⟨viaDeclaration⟩ ← observed (viaFunction.declaration = viaSignature.id) "via declaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
      let ⟨viaWord⟩ ← observed (viaSignature.id ≠ wordSignature.id) "via word distinct"
      let ⟨viaBool⟩ ← observed (viaSignature.id ≠ boolSignature.id) "via bool distinct"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "word bool distinct"
      let ⟨viaNodes⟩ ← observed (viaFunction.typedBody.nodes = viaShape.nodeList) "via nodes"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "word nodes"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "bool nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1024 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          have header := checkedHeader checked member candidateMember accepted
          have ledger := SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
            (checkProgram_success_signature_formation checked) candidateMember accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact viaShape.statementTyping traitShape program.signatures (by simp [traits]) header ledger
          · exact False.elim (viaWord (viaDeclaration.symm.trans identity))
          · exact False.elim (viaBool (viaDeclaration.symm.trans identity))
          · exact False.elim (viaWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) header ledger
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (viaBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) header ledger
        methods := by
          intro actual _member implementation method trait member methodMember lookup accepted
          simp only [implementations, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact wordMethod.statementTyping (fun _ binders => ⟨binders, .builtin .word⟩) methodMember lookup accepted
          · exact boolMethod.statementTyping (fun _ binders => ⟨binders, .builtin .bool⟩) methodMember lookup accepted }
      return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep, program, checked, trait, traitShape, traits, parameter, viaFunction, viaSignature, wordFunction, wordSignature, boolFunction, boolSignature, functions, signatures, methodCount, wordImplementation, boolImplementation, implementations, wordMethod, boolMethod, viaDeclaration, wordDeclaration, boolDeclaration, viaWord, viaBool, wordBool, viaShape, wordShape, boolShape, viaNodes, wordNodes, boolNodes}
    | _, _, _, _ => throw (IO.userError "operator original declaration inventory")

end Tests.SourceCoreEvidenceMethod
