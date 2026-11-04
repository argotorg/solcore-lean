import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Direct
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Index
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalPublicInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Method evidence tests

Evidence-passing methods: source, fixture, selection and supports.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodResults
set_option autoImplicit false
namespace Tests.SourceCoreEvidenceMethod
export Tests.SourceCoreEvidenceDirect (ScalarOutput)
end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceMethod
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
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1024, compilationFuel := 100}
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
    (CoreLowering.CallableNamedCanonicalOrder.retainedInstantiation row) header
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
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row
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
and original source declaration. Public roots additionally retain an entry. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  scalarRange : row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true
  keyOwner : row.key.declaration = signature.id
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

structure ObservedRoot (fixture : CompiledFixture) (signature : ProgramFunctionSignature) extends ObservedRow fixture signature where
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) (arguments : List TypeSystem.Ty) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id ∧ row.key.arguments = arguments)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨scalarRange⟩ ← observed (row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true) "generic complete raw range"
    let ⟨keyOwner⟩ ← observed (row.key.declaration = signature.id) "generic row key owner"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      return {
        row := row
        member := List.mem_of_find?_eq_some found
        sourceOwner := sourceOwner
        scalarRange := scalarRange
        keyOwner := keyOwner
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
        }
    | _ => throw (IO.userError "reuse unique global slot")


def observeRootRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) : IO (ObservedRoot fixture signature) := do
  let row ← observeRow fixture signature []
  match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.row.key)) with
  | none => throw (IO.userError "public root entry missing")
  | some entry =>
    let ⟨entryKey⟩ ← observed (entry.key = row.row.key) "public root entry key"
    return {toObservedRow := row, entry, entryMember := List.mem_of_find?_eq_some entryFound, entryKey}

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

theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    intro parameter replacement member
    have scalar := of_decide_eq_true (List.all_eq_true.mp observed.scalarRange (parameter, replacement) member)
    rcases scalar with rfl | rfl
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by rw [RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]; exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

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

def seed : Core.Word := Core.Word.ofNatModulo 11

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 102400
  inputValidationFuel := 1024
  outputValidationFuel := 1024 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its scalar output is obtained from the actual public execution. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 102400 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 102400 with
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
        if returned : completion.value = .word seed then
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, returned⟩
        else throw (IO.userError "generic initial output changed")

structure OperatorShape (function : CheckedFunction) (type : TypeSystem.Ty) where
  binder : TypedBinder
  read : Read function.typedBody binder type
  value : CallNode function.typedBody type
  statement : StatementNode
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  form : value.node.form = .unary .bitNot read.node.id
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono type
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some value.node.id)
  statementType : statement.type = type

def OperatorShape.nodeList {function type} (shape : OperatorShape function type) : List Node :=
  [.expression shape.read.node, .expression shape.value.node, .statement shape.statement]

def observeOperator (function : CheckedFunction) (type : TypeSystem.Ty) : IO (OperatorShape function type) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "selected operator inputs")
  let [.expression readNode, .expression node, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "selected operator nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode type
  let value ← observeCallNode function.typedBody node type
  let [requirement] := value.node.requirements | throw (IO.userError "selected operator requirements")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "operator requirements"
  let ⟨form⟩ ← observed (value.node.form = .unary .bitNot read.node.id) "operator form"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "operator inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono type) "operator binder scheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "operator binder requirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "operator roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "operator statement lookup"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some value.node.id)) "operator statement form"
  let ⟨statementType⟩ ← observed (statement.type = type) "operator statement type"
  return {binder, read, value, statement, requirement, requirements, form, inputs, binderScheme, binderRequirements, roots, statementFound, statementForm, statementType}

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  viaWordRow : ObservedRow fixture fixture.viaSignature
  viaBoolRow : ObservedRow fixture fixture.viaSignature
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.viaSignature fixture.parameter .word (.declaration fixture.trait.id)
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.viaSignature fixture.parameter .bool (.declaration fixture.trait.id)
  viaWordShape : OperatorShape viaWordRow.row.function .word
  viaBoolShape : OperatorShape viaBoolRow.row.function .bool
  wordInputScheme : wordShape.body.binder.scheme = .mono .word
  boolInputScheme : boolShape.body.binder.scheme = .mono .bool
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  viaWordNodes : viaWordRow.row.function.typedBody.nodes = viaWordShape.nodeList
  viaBoolNodes : viaBoolRow.row.function.typedBody.nodes = viaBoolShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = .word
  boolResultType : boolRow.row.function.inferredBodyType = .bool
  viaWordResultType : viaWordRow.row.function.inferredBodyType = .word
  viaBoolResultType : viaBoolRow.row.function.inferredBodyType = .bool
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  viaWordKey : viaWordRow.row.key = ⟨fixture.viaSignature.id, [.word]⟩
  viaBoolKey : viaBoolRow.row.key = ⟨fixture.viaSignature.id, [.bool]⟩
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation viaWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation viaBoolRow.row
  wordIndex : wordRow.index = 5
  boolIndex : boolRow.index = 4
  viaWordIndex : viaWordRow.index = 3
  viaBoolIndex : viaBoolRow.index = 2
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 6
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let viaWordRow ← observeRow fixture fixture.viaSignature [.word]
  let viaBoolRow ← observeRow fixture fixture.viaSignature [.bool]
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.viaSignature fixture.parameter .word (.declaration fixture.trait.id)
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.viaSignature fixture.parameter .bool (.declaration fixture.trait.id)
  let viaWordShape ← observeOperator viaWordRow.row.function .word
  let viaBoolShape ← observeOperator viaBoolRow.row.function .bool
  let ⟨wordInputScheme⟩ ← observed (wordShape.body.binder.scheme = .mono .word) "public Word input scheme"
  let ⟨boolInputScheme⟩ ← observed (boolShape.body.binder.scheme = .mono .bool) "public Bool input scheme"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "actual method program wordNodes"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "actual method program boolNodes"
  let ⟨viaWordNodes⟩ ← observed (viaWordRow.row.function.typedBody.nodes = viaWordShape.nodeList) "actual method program viaWordNodes"
  let ⟨viaBoolNodes⟩ ← observed (viaBoolRow.row.function.typedBody.nodes = viaBoolShape.nodeList) "actual method program viaBoolNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = .word) "actual method program wordResultType"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = .bool) "actual method program boolResultType"
  let ⟨viaWordResultType⟩ ← observed (viaWordRow.row.function.inferredBodyType = .word) "actual method program viaWordResultType"
  let ⟨viaBoolResultType⟩ ← observed (viaBoolRow.row.function.inferredBodyType = .bool) "actual method program viaBoolResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "actual method program wordKey"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "actual method program boolKey"
  let ⟨viaWordKey⟩ ← observed (viaWordRow.row.key = ⟨fixture.viaSignature.id, [.word]⟩) "actual method program viaWordKey"
  let ⟨viaBoolKey⟩ ← observed (viaBoolRow.row.key = ⟨fixture.viaSignature.id, [.bool]⟩) "actual method program viaBoolKey"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation viaWordRow.row) "actual method program wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation viaBoolRow.row) "actual method program boolInstantiation"
  let ⟨wordIndex⟩ ← observed (wordRow.index = 5) "actual method program wordIndex"
  let ⟨boolIndex⟩ ← observed (boolRow.index = 4) "actual method program boolIndex"
  let ⟨viaWordIndex⟩ ← observed (viaWordRow.index = 3) "actual method program viaWordIndex"
  let ⟨viaBoolIndex⟩ ← observed (viaBoolRow.index = 2) "actual method program viaBoolIndex"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 6) "actual method program globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key]) "actual method program entries"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual method program noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual method program profile"
  return {wordRow, boolRow, viaWordRow, viaBoolRow, wordShape, boolShape, viaWordShape, viaBoolShape, wordInputScheme, boolInputScheme, wordNodes, boolNodes, viaWordNodes, viaBoolNodes, wordResultType, boolResultType, viaWordResultType, viaBoolResultType, wordKey, boolKey, viaWordKey, viaBoolKey, wordInstantiation, boolInstantiation, wordIndex, boolIndex, viaWordIndex, viaBoolIndex, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodCatalog
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ClosedImplementation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters = []
  subject : implementation.head.subject = .word ∨ implementation.head.subject = .bool
  arguments : implementation.head.arguments = []
  predicates : implementation.wherePredicates = []
  methods : ∀ method, method ∈ implementation.methods → method.wherePredicates = []

theorem ClosedImplementation.formed {implementation : ProgramImplementationSignature}
    (closed : ClosedImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨closed.parameters ▸ List.nodup_nil, ?_, ?_, ?_⟩
  · intro metavariable
    rcases closed.subject with word | bool
    · simp [TypedTraitResolution.VariableOccursInPredicate, word, closed.arguments, TypeSystem.Ty.word, TypeSystem.Ty.freeVariables]
    · simp [TypedTraitResolution.VariableOccursInPredicate, bool, closed.arguments, TypeSystem.Ty.bool, TypeSystem.Ty.freeVariables]
  · intro parameter occurs
    rcases closed.subject with word | bool
    · simp [TypedTraitResolution.ParameterOccursInPredicate, word, closed.arguments,
        TypeSystem.Ty.word] at occurs
      cases occurs
    · simp [TypedTraitResolution.ParameterOccursInPredicate, bool, closed.arguments,
        TypeSystem.Ty.bool] at occurs
      cases occurs
  · intro predicate predicateMember parameter _occurs
    rw [closed.methods method member] at predicateMember
    cases predicateMember

def observeClosedImplementation (implementation : ProgramImplementationSignature) :
    IO (PLift (ClosedImplementation implementation)) := do
  let ⟨parameters⟩ ← observed (implementation.parameters = []) "method implementation parameters"
  let ⟨subject⟩ ← observed (implementation.head.subject = .word ∨ implementation.head.subject = .bool) "method implementation subject"
  let ⟨arguments⟩ ← observed (implementation.head.arguments = []) "method implementation head arguments"
  let ⟨predicates⟩ ← observed (implementation.wherePredicates = []) "method implementation predicates"
  let ⟨methods⟩ ← observed (implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true) "method predicates"
  return ⟨⟨parameters, subject, arguments, predicates, fun method member =>
    of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩

private def observeClosedImplementations : (implementations : List ProgramImplementationSignature) →
    IO (PLift (∀ implementation, implementation ∈ implementations → ClosedImplementation implementation))
  | [] => pure ⟨by intro implementation member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← observeClosedImplementation first
    let ⟨tail⟩ ← observeClosedImplementations rest
    return ⟨by
      intro implementation member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail implementation member⟩

def observeMethodCatalog (fixture : CompiledFixture) :
    IO (PLift (CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)) := do
  let ⟨closed⟩ ← observeClosedImplementations fixture.recipe.compiled.sourceProgram.signatures.implementations
  let ⟨traits⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.traits.all
    (fun trait => decide (trait.wherePredicates = [])) = true) "method trait predicates"
  return ⟨{
    parameters := fun implementation member => (closed implementation member).parameters
    formed := fun implementation member method methodMember => (closed implementation member).formed methodMember
    assumptions := by
      intro implementation member method methodMember trait traitMember
      have traitEmpty : trait.wherePredicates = [] := of_decide_eq_true (List.all_eq_true.mp traits trait traitMember)
      simp [ProgramImplementationSignature.methodAssumptions, traitEmpty,
        (closed implementation member).predicates, (closed implementation member).methods method methodMember] }⟩

theorem CompiledFixture.loaded (fixture : CompiledFixture) :
    ∃ loaded, Frontend.checkLoadedProgram loaded 1024 = .ok fixture.recipe.compiled.sourceProgram := by
  obtain ⟨loaded, _loaded, checked⟩ := checkProgram_success_load fixture.checked
  exact ⟨loaded, fixture.sameProgram.symm ▸ checked⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  wordInput : Input fixture.recipe.compiled
  wordSame : wordInput.row = observed.wordRow.row
  wordPacket : Issued wordInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  wordAligned : wordHeader.header = wordPacket.header
  wordSlot : wordHeader.header.slot = observed.wordRow.index
  wordSignature : wordHeader.header.named.signature = observed.wordRow.global
  boolInput : Input fixture.recipe.compiled
  boolSame : boolInput.row = observed.boolRow.row
  boolPacket : Issued boolInput
  boolHeader : ActualHeader fixture observed.boolRow.row
  boolAligned : boolHeader.header = boolPacket.header
  boolSlot : boolHeader.header.slot = observed.boolRow.index
  boolSignature : boolHeader.header.named.signature = observed.boolRow.global
  viaWordInput : Input fixture.recipe.compiled
  viaWordSame : viaWordInput.row = observed.viaWordRow.row
  viaWordPacket : Issued viaWordInput
  viaWordHeader : ActualHeader fixture observed.viaWordRow.row
  viaWordAligned : viaWordHeader.header = viaWordPacket.header
  viaWordSlot : viaWordHeader.header.slot = observed.viaWordRow.index
  viaWordSignature : viaWordHeader.header.named.signature = observed.viaWordRow.global
  viaBoolInput : Input fixture.recipe.compiled
  viaBoolSame : viaBoolInput.row = observed.viaBoolRow.row
  viaBoolPacket : Issued viaBoolInput
  viaBoolHeader : ActualHeader fixture observed.viaBoolRow.row
  viaBoolAligned : viaBoolHeader.header = viaBoolPacket.header
  viaBoolSlot : viaBoolHeader.header.slot = observed.viaBoolRow.index
  viaBoolSignature : viaBoolHeader.header.named.signature = observed.viaBoolRow.global

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.wordInput, given.boolInput, given.viaWordInput, given.viaBoolInput] :=
  .cons given.wordPacket (.cons given.boolPacket (.cons given.viaWordPacket (.cons given.viaBoolPacket .nil)))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨viaWordInput, viaWordSame, viaWordPacket, viaWordHeader, viaWordAligned, viaWordSlot, viaWordSignature⟩ := observed.viaWordRow.issue
  obtain ⟨viaBoolInput, viaBoolSame, viaBoolPacket, viaBoolHeader, viaBoolAligned, viaBoolSlot, viaBoolSignature⟩ := observed.viaBoolRow.issue
  exact ⟨{wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature, boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature, viaWordInput, viaWordSame, viaWordPacket, viaWordHeader, viaWordAligned, viaWordSlot, viaWordSignature, viaBoolInput, viaBoolSame, viaBoolPacket, viaBoolHeader, viaBoolAligned, viaBoolSlot, viaBoolSignature}⟩

theorem OrdinaryInventory.word_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.wordHeader.header ∈ headers given.rows := by
  rw [given.wordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.bool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.boolHeader.header ∈ headers given.rows := by
  rw [given.boolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.viaWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.viaWordHeader.header ∈ headers given.rows := by
  rw [given.viaWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.viaBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.viaBoolHeader.header ∈ headers given.rows := by
  rw [given.viaBoolAligned]
  simp [OrdinaryInventory.rows, headers]

/-- Actual instantiation metadata selects one exact ordinary row even while
other physical slots contain implementation methods. -/
theorem ObservedRow.direct_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel
      compilation values source scope id callee ids instantiation reasonAt lowered)
    (plan : compilation.plan = fixture.recipe.compiled.indexed.base.plan)
    (globals : compilation.globals = fixture.recipe.compiled.indexed.base.globals)
    (metadata : instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.row) :
    receipt.signature = observed.global ∧ receipt.index = observed.index := by
  have target := receipt.target
  simp only [plan, metadata, observed.target] at target
  have key := Except.ok.inj target
  have found := receipt.global
  rw [globals] at found
  have member : (receipt.signature, receipt.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, ?_⟩
    simp only [observed.globalKey, key, decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

theorem ObservedRow.global_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) {index : Nat} {global : SourceCoreCalls.Signature}
    (found : fixture.recipe.compiled.indexed.base.globals[index]? = some global)
    (key : global.key = observed.row.key) : global = observed.global ∧ index = observed.index := by
  have member : (global, index) ∈ fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, ?_⟩
    simp only [observed.globalKey, key, decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Public entries cover the two actual public roots. The method cache slots
need physical authority, and do not acquire ordinary Source declarations. -/
theorem OrdinaryInventory.public_coverage {fixture observed}
    (given : OrdinaryInventory fixture observed) :
    RecursiveNamedPublicRootCoverage.Coverage
      (compiled := fixture.recipe.compiled)
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (headers given.rows) := by
  intro entry member named slot found
  have entryKey : entry.key ∈ [observed.wordRow.row.key, observed.boolRow.row.key] := by
    rw [← observed.entryKeys]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have namedKey : named.signature.key = entry.key := of_decide_eq_true (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = entry.key)) found)
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled
    (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryKey
  rcases entryKey with same | same
  · have slots := observed.wordRow.global_slot selected (namedKey.trans same)
    exact ⟨given.wordHeader.header, given.word_member, given.wordSlot.trans slots.2.symm⟩
  · have slots := observed.boolRow.global_slot selected (namedKey.trans same)
    exact ⟨given.boolHeader.header, given.bool_member, given.boolSlot.trans slots.2.symm⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (NoIndirectSource)

theorem ObservedRow.record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered {plan : SourceCompilationPlan.Plan}
    {row : SourceSpecialization.SpecializedFunction}
    (target : SourceCompilationPlan.exactInstantiationKey plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)
    (record : SourceCompilationPlan.exactSpecialization plan row.key = .ok row) :
    RecursiveNamedCallSelectionCertificates.Ordered plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) := by
  intro key selected selectedTarget selectedRecord
  have sameKey := Except.ok.inj (target.symm.trans selectedTarget)
  subst key
  have sameRow := Except.ok.inj (record.symm.trans selectedRecord)
  subst selected
  exact List.map_reverse

theorem ObservedProgram.word_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.wordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.wordShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.wordInstantiation]
    exact retained_ordered observed.viaWordRow.target observed.viaWordRow.record

theorem ObservedProgram.bool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.viaBoolRow.target observed.viaBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : RootShape function signature generic parameter type trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.body.read.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same
  all_goals subst node
  · rw [shape.body.read.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same
    all_goals subst node
    · exact .inl shape.body.read.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same
    all_goals subst node
    · exact shape.body.read.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem RootShape.syntax :
    GeneralSyntax function.typedBody shape.call.value.node.id (fun inst => inst = shape.call.instantiation) := by
  refine .direct shape.call.value.found shape.call.form rfl ?_
  intro id member
  cases List.mem_singleton.mp member
  exact .leaf (.read shape.body.read.found shape.body.read.form)
end Root

section Operator
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : OperatorShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem OperatorShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.read.node ∨ node = shape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [OperatorShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem OperatorShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same
  all_goals subst node
  · rw [shape.read.form] at form; cases form
  · rw [shape.form] at form; cases form

include nodes in
theorem OperatorShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact .inl shape.read.requirements
    · exact .inr (.inr (.inr (by rw [shape.form]; trivial)))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact shape.read.coercions
    · exact shape.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem OperatorShape.syntax : GeneralSyntax function.typedBody shape.value.node.id (fun _ => False) :=
  .unary shape.value.found shape.form (.leaf (.read shape.read.found shape.read.form))
end Operator
end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodMethodSupport
/-! Every selected method uses the actual original method table. Structural
Source instantiation transports its read-and-return syntax; the real compiler
and staged selector supply all typing, dictionary and cache authority. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedMethodTerminalSupport (ReadOnlySource)

structure MethodReadBody (source : TypedSource) where
  expression : ExpressionNode
  statement : StatementNode
  name : String
  binder : Resolved.LocalId
  nodes : source.nodes = [.expression expression, .statement statement]
  roots : source.roots = [.statement statement.id]
  read : expression.form = .reference name (.local binder)
  returned : statement.form = .returnStmt (some expression.id)
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  distinct : expression.id.occurrence ≠ statement.id.occurrence

namespace MethodReadBody
variable {source : TypedSource} (shape : MethodReadBody source)

theorem expression_found : source.lookupExpression? shape.expression.id = some shape.expression := by
  simp [TypedSource.lookupExpression?, TypedSource.lookupNode?, shape.nodes, Node.occurrenceId, Node.id, NodeId.occurrenceId]

theorem statement_found : source.lookupStatement? shape.statement.id = some shape.statement := by
  simp [TypedSource.lookupStatement?, TypedSource.lookupNode?, shape.nodes, Node.occurrenceId, Node.id, NodeId.occurrenceId, shape.distinct]

include shape in
theorem only_reads : ReadOnlySource source := by
  intro id node found
  have member := (lookupExpression?_sound found).1
  rw [shape.nodes] at member
  simp only [List.mem_cons, List.not_mem_nil, Node.expression.injEq, reduceCtorEq, or_false] at member
  subst node
  exact ⟨shape.name, shape.binder, shape.read⟩

/-- Rigid substitution retains the exact read/return graph and occurrence IDs. -/
def substituted (substitution : TypeSystem.ParameterSubstitution) :
    MethodReadBody (StructuralSubstitution.applyTypedSource substitution source) where
  expression := StructuralSubstitution.applyExpressionNode substitution shape.expression
  statement := StructuralSubstitution.applyStatementNode substitution shape.statement
  name := shape.name
  binder := shape.binder
  nodes := by simp [StructuralSubstitution.applyTypedSource, shape.nodes, StructuralSubstitution.applyNode]
  roots := shape.roots
  read := by simp [StructuralSubstitution.applyExpressionNode, shape.read,
    StructuralSubstitution.applyExpressionForm, StructuralSubstitution.applyReferenceResolution]
  returned := by simp [StructuralSubstitution.applyStatementNode, shape.returned, StructuralSubstitution.applyStatementForm, StructuralSubstitution.applyExpressionNode]
  requirements := shape.requirements
  coercions := by simp [StructuralSubstitution.applyExpressionNode, shape.coercions]
  distinct := shape.distinct
end MethodReadBody

def observeMethodReadBody (source : TypedSource) : IO (MethodReadBody source) := do
  let [.expression expression, .statement statement] := source.nodes | throw (IO.userError "method original read body")
  let .reference name (.local binder) := expression.form | throw (IO.userError "method original read")
  let ⟨nodes⟩ ← observed (source.nodes = [.expression expression, .statement statement]) "method nodes"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "method roots"
  let ⟨read⟩ ← observed (expression.form = .reference name (.local binder)) "method read form"
  let ⟨returned⟩ ← observed (statement.form = .returnStmt (some expression.id)) "method return form"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "method read requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "method read coercions"
  let ⟨distinct⟩ ← observed (expression.id.occurrence ≠ statement.id.occurrence) "method distinct occurrences"
  return {expression, statement, name, binder, nodes, roots, read, returned, requirements, coercions, distinct}

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ definition, definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods →
    Nonempty (MethodReadBody definition.body.source)

private def observeMethodBodyList : (methods : List MethodDefinition) →
    IO (PLift (∀ definition, definition ∈ methods → Nonempty (MethodReadBody definition.body.source)))
  | [] => pure ⟨by intro definition member; cases member⟩
  | first :: rest => do
    let shape ← observeMethodReadBody first.body.source
    let ⟨tail⟩ ← observeMethodBodyList rest
    return ⟨by
      intro definition member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ ⟨shape⟩
      · exact tail definition member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let ⟨bodies⟩ ← observeMethodBodyList (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods
  return ⟨⟨bodies⟩⟩

/-- Only the independent actual method-instantiation relation is used to
select the original source body. The compiler cache never becomes a fake Header. -/
theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodReadBody principal.sourceBody.source) := by
  obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _implementation _method _trait _owner member _id _bodyOwner _exact _range source _result _context =>
    obtain ⟨shape⟩ := bodies.bodies definition member
    exact source ▸ ⟨shape.substituted substitution⟩

/-- Each genuinely selected method receives the actual terminal packet and a
static root. Only original syntax is inspected; the actual SourceAt and cache
retain typing, parameter allocation, dictionary and diagnostic authority. -/
theorem MethodBodies.support {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    (observed : ObservedProgram fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial fixture.recipe.compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support principal packet headers stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨shape⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = [shape.statement.id] := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [shape.roots] at roots
    simpa using roots.symm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      principal.sourceBody.source shape.expression.id principal.cached.compilation.statements := by
    rw [statements]
    exact .returning [] shape.statement_found shape.returned
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal :=
    ⟨sourceAt, shape.expression.id, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.of_read
    principal diagnostic receiver packet fixture.source_wellFormed shape.only_reads
    shape.expression_found shape.read shape.requirements shape.coercions
    (by simp [observed.noLocals]) (by simp [observed.noLocals])

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  returned : completion.value = expected

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (ObservedCall session key arguments expected) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "generic direct call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "generic direct call exhausted")
    | .ok (.succeeded completion) =>
      if returned : completion.value = expected then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "generic direct call output changed")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedCall first.completion.session observed.boolRow.row.key
    [.bool false] (.bool false)
  third : ObservedCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33)] (.word (Core.Word.ofNatModulo 33))
  fourth : ObservedCall third.completion.session observed.boolRow.row.key
    [.bool true] (.bool true)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.wordRow.toObservedRow
  let second ← observeCall first.completion.session observed.boolRow.row.key
    [.bool false] (.bool false)
  let third ← observeCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33)] (.word (Core.Word.ofNatModulo 33))
  let fourth ← observeCall third.completion.session observed.boolRow.row.key
    [.bool true] (.bool true)
  pure ⟨first, second, third, fourth⟩
end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodCommon
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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


structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.wordRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def OrdinaryInventory.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers inventory.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem OrdinaryInventory.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      (inventory.functions receiver) (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers inventory.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicPhysicalHistory.History (headers := headers inventory.rows)
    (keys := keys fixture.recipe.compiled) (functions := inventory.functions receiver)
    (receiving := receiving.result.context.registry) (anchor := inventory.wordHeader.header) session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      inventory.wordHeader.header.function.context before (.global function) arguments outcome after

theorem word_inputs {entries : List Entry} {context : SourceSemantics.Context} (value : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word]
      [.word value] [.word value] := by
  exact .cons (.data
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil

theorem word_simple (value : Core.Word) :
    ∀ item ∈ ([.word value] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  have same := List.mem_singleton.mp member
  subst item
  exact .word value

theorem bool_inputs {entries : List Entry} {context : SourceSemantics.Context} (value : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.bool]
      [.bool value] [.bool value] := by
  exact .cons (.data
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩) .nil

theorem bool_simple (value : Bool) :
    ∀ item ∈ ([.bool value] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  have same := List.mem_singleton.mp member
  subst item
  exact .bool value

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodOrdinarySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport (Support)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include rows receiver methods in
theorem ActualHeader.direct_support {signature generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (row : ObservedRow fixture signature)
    (shape : RootShape row.row.function signature generic parameter type trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (supported : Supported fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (actual : ActualHeader fixture row.row)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
        shape.call.instantiation = .ok signature.key →
      fixture.recipe.compiled.indexed.base.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.call.value.node.id
    shape.body.statement shape.body.roots shape.body.statementFound (by simpa only [shape.result] using shape.body.statementForm)
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun inst => inst = shape.call.instantiation) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.of_actual
    (directSites := fun inst => inst = shape.call.instantiation)
    terminal diagnostic receiver fixture.source_wellFormed (fun _ same => same ▸ supported) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows ?_
    (by rw [actual.source]; exact shape.no_indirect nodes) checked ?_ methods
    (actualStagePrepared fixture) point⟩
  · intro inst same index signature target global
    subst inst
    exact covered index signature target global
  · rw [fixture.sameProgram]
    exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

include rows receiver methods in
theorem ActualHeader.operator_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : OperatorShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.value.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim)
    (by rw [actual.source]; exact shape.no_indirect nodes) checked ?_ methods
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ObservedProgram.wordBool {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    observed.wordRow.index ≠ observed.boolRow.index := by
  rw [observed.wordIndex, observed.boolIndex]
  decide

theorem ObservedProgram.wordViaWord {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    observed.wordRow.index ≠ observed.viaWordRow.index := by
  rw [observed.wordIndex, observed.viaWordIndex]
  decide

theorem ObservedProgram.wordViaBool {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    observed.wordRow.index ≠ observed.viaBoolRow.index := by
  rw [observed.wordIndex, observed.viaBoolIndex]
  decide

theorem ObservedProgram.boolViaWord {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    observed.boolRow.index ≠ observed.viaWordRow.index := by
  rw [observed.boolIndex, observed.viaWordIndex]
  decide

theorem ObservedProgram.boolViaBool {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    observed.boolRow.index ≠ observed.viaBoolRow.index := by
  rw [observed.boolIndex, observed.viaBoolIndex]
  decide

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

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (viaWordHeader : ActualHeader fixture observed.viaWordRow.row)
    (viaBoolHeader : ActualHeader fixture observed.viaBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, viaWordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.viaWordRow observed.wordViaWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, viaBoolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.viaBoolRow observed.wordViaBool) headerKey.symm)

theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (viaWordHeader : ActualHeader fixture observed.viaWordRow.row)
    (viaBoolHeader : ActualHeader fixture observed.viaBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, viaWordHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.viaWordRow observed.boolViaWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, viaBoolHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.viaBoolRow observed.boolViaBool) headerKey.symm)

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
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (viaWordHeader : ActualHeader fixture observed.viaWordRow.row)
    (viaBoolHeader : ActualHeader fixture observed.viaBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader viaWordHeader viaBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, viaWordHeader.header, viaBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader viaWordHeader viaBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.word_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.word_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

theorem ActualHeader.bool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.output = .bool := by
  have projected := actual.aligned.projection
  rw [actual.bool_result_type] at projected
  exact (Except.ok.inj projected).symm

def ObservedStages.descriptor_at {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (stages : ObservedStages fixture observed)
    (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.key]
  exact stages.descriptor

 theorem OrdinaryInventory.header_list {fixture observed} (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows =
      [inventory.wordHeader.header, inventory.boolHeader.header, inventory.viaWordHeader.header, inventory.viaBoolHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.wordAligned, inventory.boolAligned, inventory.viaWordAligned, inventory.viaBoolAligned]

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodSeed
/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.viaWordInput, inventory.viaBoolInput].map (fun input => input.prepared.index)).Nodup)
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal inventory.wordHeader.header)
    (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure inventory.wordHeader.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        inventory.wordHeader.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          receiver.completion.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiver.completion.result.diagnostics) budget) (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ state : RetainedState inventory receiver first.completion.session [],
      SourceCall inventory inventory.wordHeader.header
        (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
        ⟨[]⟩ [.word seed] (.value (.word seed)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 102400 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    exact word_simple seed
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    prepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.viaWordHeader inventory.viaBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs inventory.rows session inventory.wordHeader.header.function.context
      (inventory.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed] [.word seed] := by
    rw [inventory.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt inventory.wordHeader.header inventory.wordInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global inventory.wordPacket.header.named.specialized inventory.wordInput.prepared.available)) := by
    rw [inventory.wordAligned]
    exact inventory.wordPacket.sourceAt
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalArguments.initial_arguments
      (inputs := [inventory.wordInput, inventory.boolInput, inventory.viaWordInput, inventory.viaBoolInput])
      (rows := inventory.rows) (distinct := distinct)
      (profile := observed.profile) (completion := receiver.completion)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (started := started) (inputReceipts := inputs) (metadata := metadata)
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    inventory.wordHeader.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := receiver.completion)
      (profile := observed.profile) (packet := packet) (reflectsBodies := reflectsBodies)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (wellFormed := fixture.source_wellFormed)
      (selected := selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := started)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
      first.started checkpointAt first.executed (stages.descriptor_at inventory.wordHeader)
  obtain ⟨returnedCaller, _related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_success rfl started selected succeeded result
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, inventory.wordHeader.word_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.returned) inventory.wordHeader.word_output result
  let state : RetainedState inventory receiver first.completion.session [] := {
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
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨state, inventory.wordInput.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodStep
/-! Actual named calls with Word or Bool results continue the same retained session and Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.finished_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal request.header)
    (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure request.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        request.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          state.receiving.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics) budget)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState inventory receiver call.completion.session entries,
      SourceCall inventory request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (rows := inventory.rows) (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history.semantic)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (profile := observed.profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (packet := packet) (reflectsBodies := reflectsBodies)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (wellFormed := fixture.source_wellFormed)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_success
    rfl request.started request.selected succeeded result
  have physicalRetained := state.history.after_result result retained
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans call.returned) represented
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState inventory receiver call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨next, request.rawD, request.function, sourceSize, request.sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments scalar.publicValue)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = scalar.publicValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState inventory receiver completion.session entries, returned.heap = after

theorem forward_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal request.header)
    (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure request.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        request.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          state.receiving.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics) budget)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) inventory receiver scalar call after := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (rows := inventory.rows) (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history.semantic)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (profile := observed.profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (packet := packet) (preservesBodies := preservesBodies)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (wellFormed := fixture.source_wellFormed)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked
      state.receiving.result.context.registry (inventory.functions receiver)
      finalMap finalWorld request.header.function.resultType scalar.source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have nativeScalar : payload = scalar.native := by
    rw [nativeType] at representedResult
    exact scalar.native_value representedResult
  have shape : SourceCorePublicOutputShapes.Output fixture.recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) fixture.recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_success
    rfl request.started request.selected exported result
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : RetainedState inventory receiver completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  rw [rawType] at requested
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodInitialForward
/-! Initial Source success determines sufficient execution and export budgets
at the original public checkpoint, retaining all actual installed method cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧ completion.value = .word seed ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState inventory receiver completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.viaWordInput, inventory.viaBoolInput].map
      (fun input => input.prepared.index)).Nodup)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow)
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal inventory.wordHeader.header)
    (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure inventory.wordHeader.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        inventory.wordHeader.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          receiver.completion.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiver.completion.result.diagnostics) budget)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall inventory inventory.wordHeader.header invocation ⟨[]⟩ [.word seed] (.value (.word seed)) after) :
    InitialForwardAt inventory receiver first after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 102400 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    exact started.simple_registry (booted.registry_at initial) (word_simple seed)
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    fixture.recipePrepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.viaWordHeader inventory.viaBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs inventory.rows session inventory.wordHeader.header.function.context
      (inventory.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [inventory.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry, receiver.registry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalArguments.initial_arguments
      (inputs := [inventory.wordInput, inventory.boolInput, inventory.viaWordInput, inventory.viaBoolInput])
      (rows := inventory.rows) (distinct := distinct) (completion := receiver.completion)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (started := started) (inputReceipts := inputs) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := receiver.completion)
      (profile := observed.profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (packet := packet) (preservesBodies := preservesBodies)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := caller.physical) (wellFormed := fixture.source_wellFormed)
      (selected := selected) (caller := caller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := (RecursiveNamedPublicReturnedValues.header_context_supports
        inventory.wordHeader.header inventory.wordHeader.header fixture.source_wellFormed).2) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked
      receiver.completion.result.context.registry (inventory.functions receiver)
      finalMap finalWorld inventory.wordHeader.header.function.resultType (.word seed) payload inventory.wordHeader.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have nativeWord : payload = .word seed := by
    rw [inventory.wordHeader.word_output] at representedResult
    exact Tests.SourceCoreEvidenceDirect.ScalarOutput.native_value (.word seed) representedResult
  have shape : SourceCorePublicOutputShapes.Output fixture.recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) fixture.recipe.program.layouts.definitions inventory.wordHeader.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [receiver.registry, ← startupRegistry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  have checkpointReady := started.original.initial_registry.exportsReady
    (sessionAt.exportsReady_iff.mp (ready.exportsReady first.authority))
  obtain ⟨requiredOutput, exports⟩ := first.checkpoint.output_succeeded_uniform
    checkpointAt atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, _related, retained⟩ := RecursiveNamedPublicFunctionHistory.first_success
    (anchor := inventory.wordHeader.header) rfl started selected exported result
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry := started.returned_registry exported
  rw [startupRegistry, ← receiver.registry] at returnedRegistry
  let returned : RetainedState inventory receiver completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  rw [inventory.wordHeader.word_result_type] at requested
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, viaWordInput, viaBoolInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers toOrdinaryInventory.rows → Terminal header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    Support (headers := headers toOrdinaryInventory.rows)
      (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (terminals header member)
  wordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named wordHeader.header.named.signature.key)
  boolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named boolHeader.header.named.signature.key)

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.wordInput.prepared.index = 5 ∧ given.boolInput.prepared.index = 4 ∧
      given.viaWordInput.prepared.index = 3 ∧ given.viaBoolInput.prepared.index = 2 := by
  have word : given.wordHeader.header.slot = given.wordInput.prepared.index := by
    rw [given.wordAligned]; exact given.wordPacket.aligned.slot
  have bool : given.boolHeader.header.slot = given.boolInput.prepared.index := by
    rw [given.boolAligned]; exact given.boolPacket.aligned.slot
  have viaWord : given.viaWordHeader.header.slot = given.viaWordInput.prepared.index := by
    rw [given.viaWordAligned]; exact given.viaWordPacket.aligned.slot
  have viaBool : given.viaBoolHeader.header.slot = given.viaBoolInput.prepared.index := by
    rw [given.viaBoolAligned]; exact given.viaBoolPacket.aligned.slot
  exact ⟨word.symm.trans (given.wordSlot.trans observed.wordIndex),
    bool.symm.trans (given.boolSlot.trans observed.boolIndex),
    viaWord.symm.trans (given.viaWordSlot.trans observed.viaWordIndex),
    viaBool.symm.trans (given.viaBoolSlot.trans observed.viaBoolIndex)⟩

/-- Four ordinary headers are issued at their real physical slots. The two
implementation slots are supplied by the separate method selection support. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨wordTerminal, ⟨wordSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.wordRow.toObservedRow observed.wordShape observed.wordNodes observed.noLocals observed.word_supported
    given.wordHeader (by
      intro index signature target global
      rw [observed.wordInstantiation, observed.viaWordRow.target] at target
      have same := observed.viaWordRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.viaWordHeader.header, given.viaWord_member, given.viaWordSlot.trans same.2.symm,
        given.viaWordSignature.trans same.1.symm⟩)
  obtain ⟨boolTerminal, ⟨boolSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.boolRow.toObservedRow observed.boolShape observed.boolNodes observed.noLocals observed.bool_supported
    given.boolHeader (by
      intro index signature target global
      rw [observed.boolInstantiation, observed.viaBoolRow.target] at target
      have same := observed.viaBoolRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.viaBoolHeader.header, given.viaBool_member, given.viaBoolSlot.trans same.2.symm,
        given.viaBoolSignature.trans same.1.symm⟩)
  obtain ⟨viaWordTerminal, ⟨viaWordSupport⟩⟩ := ActualHeader.operator_support given.rows receiver methods
    observed.viaWordRow observed.viaWordShape observed.viaWordNodes observed.noLocals given.viaWordHeader
  obtain ⟨viaBoolTerminal, ⟨viaBoolSupport⟩⟩ := ActualHeader.operator_support given.rows receiver methods
    observed.viaBoolRow observed.viaBoolShape observed.viaBoolNodes observed.noLocals given.viaBoolHeader
  let property := fun header => Σ terminal : Terminal header,
    Support (headers := headers given.rows)
      (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header terminal
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨⟨wordTerminal, wordSupport⟩⟩
    · exact ⟨⟨boolTerminal, boolSupport⟩⟩
    · exact ⟨⟨viaWordTerminal, viaWordSupport⟩⟩
    · exact ⟨⟨viaBoolTerminal, viaBoolSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by simp only [List.map_cons, List.map_nil, given.indices.1, given.indices.2.1,
      given.indices.2.2.1, given.indices.2.2.2]; decide
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    wordDescriptor := by rw [given.wordSignature, observed.wordRow.globalKey]; exact wordStages.descriptor
    boolDescriptor := by rw [given.boolSignature, observed.boolRow.globalKey]; exact boolStages.descriptor
  }⟩

end Tests.SourceCoreEvidenceMethod
end
