import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.Test.SourceSemantics.CoreLowering.Method.OriginFixture
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.EligibleSelected

/-!
# Public coercion tests

Coerced calls from cached source graphs through their public sessions.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicResults
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
export Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults (ScalarOutput)
end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev Required := Tests.SourceCoreEvidenceScoped.Required
abbrev observeRequired := Tests.SourceCoreEvidenceScoped.observeRequired
abbrev IdentityShape := Tests.SourceCoreMethodOriginEvidence.IdentityShape
abbrev observeIdentity := Tests.SourceCoreMethodOriginEvidence.observeIdentity
abbrev UseShape := Tests.SourceCoreMethodOriginEvidence.UseShape
abbrev observeUse := Tests.SourceCoreMethodOriginEvidence.observeUse
def predicate (trait : ProgramTraitId) (type : TypeSystem.Ty) : ProgramPredicate := ⟨trait,type,[]⟩
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

structure CoercionProfile (trait : ProgramTraitSignature) where
  method : ProgramTraitMethodSignature
  fromParameter : TypeSystem.TypeParameterId
  toParameter : TypeSystem.TypeParameterId
  name : trait.name = "Coerce"
  parameters : trait.parameters = [fromParameter,toParameter]
  methodUnique : trait.methods.filter (fun method => method.name == "coerce") = [method]
  inputs : method.parameterTypes.map (TypeSystem.ParameterSubstitution.apply [(fromParameter,.bool),(toParameter,.word)]) = [.bool]
  returns : method.returnTypes.map (TypeSystem.ParameterSubstitution.apply [(fromParameter,.bool),(toParameter,.word)]) = [.word]
  predicates : method.wherePredicates = []

theorem CoercionProfile.typed {trait} (profile : CoercionProfile trait) {context : SourceSemantics.Context}
    (member : trait ∈ context.signatures.traits) :
    CoercionProfileInstantiates context .bool .word ⟨.declaration trait.id,.bool,[.word]⟩ [] := by
  simpa only [profile.predicates, List.map_nil] using
    (CoercionProfileInstantiates.intro member profile.name profile.parameters profile.methodUnique profile.inputs profile.returns)

def observeProfile (trait : ProgramTraitSignature) : IO (CoercionProfile trait) := do
  let [fromParameter,toParameter] := trait.parameters | throw (IO.userError "Coerce parameters")
  match methods : trait.methods with
  | [method] =>
    let ⟨name⟩ ← observed (trait.name = "Coerce") "Coerce name"
    let ⟨parameters⟩ ← observed (trait.parameters = [fromParameter,toParameter]) "Coerce parameters"
    let ⟨methodName⟩ ← observed (method.name = "coerce") "Coerce method"
    have methodUnique : trait.methods.filter (fun method => method.name == "coerce") = [method] := by simp [methods,methodName]
    let ⟨inputs⟩ ← observed (method.parameterTypes.map (TypeSystem.ParameterSubstitution.apply [(fromParameter,.bool),(toParameter,.word)]) = [.bool]) "Coerce inputs"
    let ⟨returns⟩ ← observed (method.returnTypes.map (TypeSystem.ParameterSubstitution.apply [(fromParameter,.bool),(toParameter,.word)]) = [.word]) "Coerce returns"
    let ⟨predicates⟩ ← observed (method.wherePredicates = []) "Coerce predicates"
    return {method,fromParameter,toParameter,name,parameters,methodUnique,inputs,returns,predicates}
  | _ => throw (IO.userError "Coerce methods")

structure CoercedCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (argument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function .bool .bool)
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  raw : node.rawType = .bool
  type : node.type = .word
  step : CoercionStep
  stepSource : step.source = .bool
  stepTarget : step.target = .word
  stepMethods : step.methodRequirements = []
  coercions : node.coercions = [step]
  requirement : RequirementId
  requirements : node.requirements = [step.requirement,requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : node.form = .call callee.node.id [argument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)], .function (.parameter parameter) (.parameter parameter)⟩
  inputs : signature.parameterTypes = [.parameter parameter]
  returns : signature.returnTypes = [.parameter parameter]
  exact : instantiation = ⟨signature.id, [(parameter, .bool)], .function .bool .bool, [predicate trait .bool], signature.parameterComptime, signature.returnComptime⟩

theorem CoercedCall.typed {source signature parameter argument trait}
    (call : CoercedCall source signature parameter argument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context .bool)
    (typed : ExpressionHasType source context argument .bool)
    (required : RequirementProves context call.requirement (predicate trait .bool))
    (path : CoercionPathValid context .bool .word [call.step]) :
    ExpressionHasType source context call.node.id .word := by
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
  have application : DeclarationApplicationValid context call.instantiation [.bool] .bool [predicate trait .bool] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.node.id call.node.type := by
    refine .intro (lookupExpression?_sound call.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons typed (.nil _)))
      call.raw firstFormed (call.type.symm ▸ (⟨firstFormed.1,.builtin .word⟩ : TypeAdmissible context .word)) ?_
    rw [call.requirements, call.coercions, call.type]
    exact .directCall (.intro path (.nil _) (.cons required .nil) rfl (by simp [coercionRequirementIds, CoercionStep.requirements,call.stepMethods]))
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.node.id type) call.type) typed

private theorem builtin_word_evidence (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntWordRule) (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

structure WordLiteral (function : CheckedFunction) where
  node : ExpressionNode
  spelling : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  validated : SourceCoreElaboration.WordIntegerLiteral
  found : function.typedBody.lookupExpression? node.id = some node
  form : node.form = .integerLiteral spelling resolution
  raw : node.rawType = .word
  accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution = .ok validated

theorem WordLiteral.typed {function : CheckedFunction} (literal : WordLiteral function)
    {context : SourceSemantics.Context} (word : TypeAdmissible context .word)
    (ledger : context.solvedRequirements = function.solvedRequirements) :
    ExpressionHasType function.typedBody context literal.node.id .word := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound literal.accepted
  obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.word literal.accepted
  have member : row ∈ function.solvedRequirements.filter (fun row => decide (row.id = literal.resolution.requirement)) := by
    rw [selected]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have proves : RequirementProves context literal.resolution.requirement
      (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) := by
    refine ⟨row, ⟨ledger ▸ member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
    rw [evidence, predicate]
    change RetainedEvidenceValid _ _ (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) _
    rw [metadata.targetType]
    simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_word_evidence context
  have valid : IntegerLiteralValid context literal.spelling literal.resolution :=
    .word metadata.meaning metadata.targetType proves
  have typed : ExpressionHasType function.typedBody context literal.node.id literal.node.type := by
    refine .intro (lookupExpression?_sound literal.found)
      (literal.form ▸ ExpressionFormHasRawType.integerLiteral valid)
      (literal.raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ word)
      (metadata.nodeType.symm ▸ word) ?_
    rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
    exact .ordinary (by intro id member; have same := List.mem_singleton.mp member; exact same ▸ valid.requirement_valid) (.nil _) rfl
  exact metadata.nodeType ▸ typed

def observeWordLiteral (function : CheckedFunction) (node : ExpressionNode) : IO (WordLiteral function) := do
  let .integerLiteral spelling resolution := node.form | throw (IO.userError "word integer literal")
  let ⟨found⟩ ← observed (function.typedBody.lookupExpression? node.id = some node) "word literal lookup"
  let ⟨form⟩ ← observed (node.form = .integerLiteral spelling resolution) "word literal form"
  let ⟨raw⟩ ← observed (node.rawType = .word) "word literal raw type"
  match accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution with
  | .error error => throw (IO.userError (reprStr error))
  | .ok validated => return {node,spelling,resolution,validated,found,form,raw,accepted}

structure MethodShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .bool
  first : WordLiteral function
  second : WordLiteral function
  value : TypedNode function.typedBody .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputs : function.typedBody.inputs = [binder]
  inputTypes : signature.parameterTypes = [.bool]
  returns : signature.returnTypes = [.word]
  binderRequirements : binder.schemeRequirements = []
  conditional : value.node.form = .conditional read.node.id first.node.id second.node.id
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some value.node.id)
  statementType : statement.type = .word

def MethodShape.nodeList {function signature} (shape : MethodShape function signature) : List Node :=
  [.expression shape.read.node,.expression shape.first.node,.expression shape.second.node,.expression shape.value.node,.statement shape.statement]

theorem MethodShape.statementTyping {function signature} (shape : MethodShape function signature)
    (signatures : ProgramSignatures) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := ⟨.word,true,true,.returned⟩
  refine ⟨BodyFacts.singleton facts,rfl,?_⟩
  intro lexical extension
  rw [shape.inputs,shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed,head.context_fields.2.2.1]
      simp [checkedBodyContext,declarationContext,Context.ofSignatures,Context.forDeclaration,
        Context.withAssumptions,Context.withSolvedRequirements,Context.withResidualTypeVariables,shape.parameters]
    have bool : TypeAdmissible lexical .bool := ⟨binders,.builtin .bool⟩
    have word : TypeAdmissible lexical .word := ⟨binders,.builtin .word⟩
    have ledger : lexical.solvedRequirements = function.solvedRequirements := head.context_fields.2.2.2.2
    have read := shape.read.typed scheme shape.binderRequirements bool head.local_self head.local_scheme_requirements_self
    have first := shape.first.typed word ledger
    have second := shape.second.typed word ledger
    have typed : ExpressionHasType function.typedBody lexical shape.value.node.id .word := by
      apply Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.value.node.id type) shape.value.type)
      refine .intro (lookupExpression?_sound shape.value.found)
        (shape.conditional ▸ ExpressionFormHasRawType.conditional read first second) shape.value.raw word (shape.value.type.symm ▸ word) ?_
      rw [shape.value.requirements,shape.value.coercions,shape.value.type]
      exact .ordinary (by intro id member;cases member) (.nil _) rfl
    exact ⟨_,.singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm typed shape.statementType)⟩

def observeMethod (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (MethodShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "coercion method binder")
  let [.expression read,.expression first,.expression second,.expression value,.statement statement] := function.typedBody.nodes
    | throw (IO.userError "coercion method nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .bool
  let first ← observeWordLiteral function first
  let second ← observeWordLiteral function second
  let value ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody value .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "coercion method parameters"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "coercion method inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.bool]) "coercion method input types"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "coercion method returns"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "coercion method binder requirements"
  let ⟨conditional⟩ ← observed (value.node.form = .conditional read.node.id first.node.id second.node.id) "coercion method conditional"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "coercion method roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "coercion method statement"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some value.node.id)) "coercion method return"
  let ⟨statementType⟩ ← observed (statement.type = .word) "coercion method statement type"
  return {binder,read,first,second,value,statement,parameters,inputs,inputTypes,returns,binderRequirements,conditional,roots,statementFound,statementForm,statementType}

structure FactoryShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (mark coercion : ProgramTraitSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .bool
  call : CoercedCall function.typedBody generic parameter read.node.id (.declaration mark.id)
  profile : CoercionProfile coercion
  callRequired : Required function call.requirement (predicate (.declaration mark.id) .bool)
  coercionRequired : Required function call.step.requirement ⟨.declaration coercion.id,.bool,[.word]⟩
  innerReturn : StatementNode
  expression : TypedNode function.typedBody (.function .unit .word)
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputs : function.typedBody.inputs = [binder]
  inputTypes : signature.parameterTypes = [.bool]
  returns : signature.returnTypes = [.function .unit .word]
  binderRequirements : binder.schemeRequirements = []
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some call.node.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.node.form = .lambda [] .word [innerReturn.id]
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some expression.node.id)
  statementType : statement.type = .function .unit .word

def FactoryShape.nodeList {function signature generic parameter mark coercion}
    (shape : FactoryShape function signature generic parameter mark coercion) : List Node :=
  [.expression shape.read.node,.expression shape.call.callee.node,.expression shape.call.node,
    .statement shape.innerReturn,.expression shape.expression.node,.statement shape.statement]

theorem FactoryShape.statementTyping {function signature generic parameter mark coercion}
    (shape : FactoryShape function signature generic parameter mark coercion)
    (signatures : ProgramSignatures) (genericMember : generic ∈ signatures.functions)
    (coercionMember : coercion ∈ signatures.traits)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := ⟨.function .unit .word,true,true,.returned⟩
  refine ⟨BodyFacts.singleton facts,rfl,?_⟩
  intro lexical extension
  rw [shape.inputs,shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed,head.context_fields.2.2.1]
      simp [checkedBodyContext,declarationContext,Context.ofSignatures,Context.forDeclaration,
        Context.withAssumptions,Context.withSolvedRequirements,Context.withResidualTypeVariables,shape.parameters]
    have bool : TypeAdmissible lexical .bool := ⟨binders,.builtin .bool⟩
    have callable : TypeAdmissible lexical (.function .unit .word) := ⟨binders,.function (.builtin .unit) (.builtin .word)⟩
    have current := ledger.transportContext head.context_fields.1 head.context_fields.2.2.2.1 head.context_fields.2.2.2.2
    have required := shape.callRequired.proves current head.context_fields.2.2.2.2 shape.noTemplates
    have coercionRequired := shape.coercionRequired.proves current head.context_fields.2.2.2.2 shape.noTemplates
    have fields : lexical.signatures = signatures := head.context_fields.1
    have profile := shape.profile.typed (fields.symm ▸ coercionMember)
    have path : CoercionPathValid lexical .bool .word [shape.call.step] := by
      have valid : CoercionStepValid lexical shape.call.step := by
        refine .intro (by simpa only [shape.call.stepSource,shape.call.stepTarget] using profile) ?_
        rw [shape.call.stepMethods]
        exact .cons coercionRequired .nil
      simpa only [shape.call.stepSource,shape.call.stepTarget] using
        (CoercionPathValid.cons valid (CoercionPathValid.nil shape.call.step.target))
    have read := shape.read.typed scheme shape.binderRequirements bool head.local_self head.local_scheme_requirements_self
    have call := shape.call.typed (fields.symm ▸ genericMember) bool read required path
    have typed : ExpressionHasType function.typedBody lexical shape.expression.node.id (.function .unit .word) := by
      apply Eq.mp (congrArg (fun type => ExpressionHasType function.typedBody lexical shape.expression.node.id type) shape.expression.type)
      refine .intro (lookupExpression?_sound shape.expression.found)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm call shape.innerReturnType))
          (by exact ⟨rfl,rfl,.inl ⟨rfl,rfl⟩⟩)) shape.expression.raw callable (shape.expression.type.symm ▸ callable) ?_
      rw [shape.expression.requirements,shape.expression.coercions,shape.expression.type]
      exact .ordinary (by intro id member;cases member) (.nil _) rfl
    exact ⟨_,.singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm typed shape.statementType)⟩
def observeCoercedCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (argument : ExpressionId)
    (callee node : ExpressionNode) (trait : ProgramTraitId) : IO (CoercedCall source signature parameter argument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function .bool .bool)
  let [step] := node.coercions | throw (IO.userError "coercion path singleton")
  let [_,requirement] := node.requirements | throw (IO.userError "coerced direct requirements")
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "coerced direct callee")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "coerced direct found"
  let ⟨raw⟩ ← observed (node.rawType = .bool) "coerced direct raw"
  let ⟨type⟩ ← observed (node.type = .word) "coerced direct type"
  let ⟨stepSource⟩ ← observed (step.source = .bool) "coercion source"
  let ⟨stepTarget⟩ ← observed (step.target = .word) "coercion target"
  let ⟨stepMethods⟩ ← observed (step.methodRequirements = []) "coercion method requirements"
  let ⟨coercions⟩ ← observed (node.coercions = [step]) "coercion path"
  let ⟨requirements⟩ ← observed (node.requirements = [step.requirement,requirement]) "ordered coercion and call requirements"
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "coerced direct callee form"
  let ⟨form⟩ ← observed (node.form = .call callee.node.id [argument] (.declaration instantiation)) "coerced direct form"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[parameter],[predicate trait (.parameter parameter)],.function (.parameter parameter) (.parameter parameter)⟩) "keep scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter parameter]) "keep inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter parameter]) "keep returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id,[(parameter,.bool)],.function .bool .bool,[predicate trait .bool],signature.parameterComptime,signature.returnComptime⟩) "keep instantiation"
  return {callee,node,found,raw,type,step,stepSource,stepTarget,stepMethods,coercions,requirement,requirements,name,instantiation,calleeForm,form,scheme,inputs,returns,exact}

def observeFactory (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (mark coercion : ProgramTraitSignature) :
    IO (FactoryShape function signature generic parameter mark coercion) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "make binder")
  let [.expression read,.expression callee,.expression call,.statement innerReturn,.expression expression,.statement statement] := function.typedBody.nodes
    | throw (IO.userError "make nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .bool
  let call ← observeCoercedCall function.typedBody generic parameter read.node.id callee call (.declaration mark.id)
  let profile ← observeProfile coercion
  let callRequired ← observeRequired function call.requirement (predicate (.declaration mark.id) .bool)
  let coercionRequired ← observeRequired function call.step.requirement ⟨.declaration coercion.id,.bool,[.word]⟩
  let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody expression (.function .unit .word)
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "make parameters"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "make inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.bool]) "make input types"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "make returns"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "make binder requirements"
  let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "make templates"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "make inner return"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some call.node.id)) "make inner return form"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "make inner return type"
  let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] .word [innerReturn.id]) "make lambda"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "make roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "make return"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some expression.node.id)) "make return form"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "make return type"
  return {binder,read,call,profile,callRequired,coercionRequired,innerReturn,expression,statement,parameters,inputs,inputTypes,returns,binderRequirements,noTemplates,innerReturnFound,innerReturnForm,innerReturnType,lambda,roots,statementFound,statementForm,statementType}

structure ImplementationShape (program : CheckedProgram) (implementation : ProgramImplementationSignature) where
  method : ProgramImplMethodSignature
  trait : ProgramTraitSignature
  function : CheckedFunction
  methods : implementation.methods = [method]
  traitLookup : program.signatures.trait? method.traitMethod.trait = some trait
  checked : checkFunctionBody program.environment program.signatures
    (implementation.functionSignatureOfMethodWithTrait trait method) 1024 = .ok function
  shape : MethodShape function (implementation.functionSignatureOfMethodWithTrait trait method)

theorem ImplementationShape.statementTyping {program implementation} (given : ImplementationShape program implementation)
    {method trait function} (member : method ∈ implementation.methods)
    (lookup : program.signatures.trait? method.traitMethod.trait = some trait)
    (checked : checkFunctionBody program.environment program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) 1024 = .ok function) :
    CheckedBodyStatementsHaveType program.signatures (implementation.functionSignatureOfMethodWithTrait trait method) function := by
  rw [given.methods] at member
  cases List.mem_singleton.mp member
  have sameTrait := Option.some.inj (lookup.symm.trans given.traitLookup)
  subst trait
  have sameFunction := Except.ok.inj (checked.symm.trans given.checked)
  subst function
  exact given.shape.statementTyping program.signatures

def observeImplementation (program : CheckedProgram) (implementation : ProgramImplementationSignature) :
    IO (ImplementationShape program implementation) := do
  match methods : implementation.methods with
  | [method] =>
    match traitLookup : program.signatures.trait? method.traitMethod.trait with
    | none => throw (IO.userError "coercion method trait")
    | some trait =>
      match checked : checkFunctionBody program.environment program.signatures
          (implementation.functionSignatureOfMethodWithTrait trait method) 1024 with
      | .error error => throw (IO.userError (reprStr error))
      | .ok function =>
        let shape ← observeMethod function (implementation.functionSignatureOfMethodWithTrait trait method)
        return {method,trait,function,methods,traitLookup,checked,shape}
  | _ => throw (IO.userError "coercion implementation methods")

def content : String := String.intercalate "\n" [
  "trait Mark<T> {}", "impl Mark<Bool> {}",
  "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
  "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { return value ? 41 : 7; } }",
  "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
  "function make(value: Bool) returns (function() returns (Word)) { return lam() -> Word { return keep(value); }; }",
  "function use(f: function() returns (Word)) returns (Word) { return f(); }"]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc",externalLibraries := [],mainSources := [{path := "main.solc",content}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1024 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  mark : ProgramTraitSignature
  coercion : ProgramTraitSignature
  traits : program.signatures.traits = [mark,coercion]
  markImplementation : ProgramImplementationSignature
  markMethods : markImplementation.methods = []
  implementation : ProgramImplementationSignature
  implementations : program.signatures.implementations = [markImplementation,implementation]
  methodShape : ImplementationShape program implementation
  parameter : TypeSystem.TypeParameterId
  keepFunction : CheckedFunction
  keepSignature : ProgramFunctionSignature
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  useFunction : CheckedFunction
  useSignature : ProgramFunctionSignature
  functions : program.functions = [keepFunction,makeFunction,useFunction]
  signatures : program.signatures.functions = [keepSignature,makeSignature,useSignature]
  keepDeclaration : keepFunction.declaration = keepSignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  useDeclaration : useFunction.declaration = useSignature.id
  keepShape : IdentityShape keepFunction keepSignature (.parameter parameter)
  makeShape : FactoryShape makeFunction makeSignature keepSignature parameter mark coercion
  useShape : UseShape useFunction useSignature .word
  keepNodes : keepFunction.typedBody.nodes = keepShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList
  useNodes : useFunction.typedBody.nodes = useShape.nodeList

private theorem checkedHeader {program : CheckedProgram} (checked : checkProgram workspace 1024 = .ok program)
    {function signature} (member : function ∈ program.functions) (signatureMember : signature ∈ program.signatures.functions)
    (accepted : checkFunctionBody program.environment program.signatures signature 1024 = .ok function) :
    CheckedBodyHeaderWellFormed program.signatures signature function := by
  obtain ⟨other,otherMember,header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked member
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
    | [keepFunction,makeFunction,useFunction],[keepSignature,makeSignature,useSignature],
        [mark,coercion],[markImplementation,implementation] =>
      let [parameter] := keepSignature.scheme.parameters | throw (IO.userError "keep parameter")
      let keepShape ← observeIdentity keepFunction keepSignature (.parameter parameter)
      let makeShape ← observeFactory makeFunction makeSignature keepSignature parameter mark coercion
      let useShape ← observeUse useFunction useSignature .word
      let methodShape ← observeImplementation program implementation
      let ⟨markMethods⟩ ← observed (markImplementation.methods = []) "Mark methods"
      let ⟨keepDeclaration⟩ ← observed (keepFunction.declaration = keepSignature.id) "keep declaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨useDeclaration⟩ ← observed (useFunction.declaration = useSignature.id) "use declaration"
      let ⟨keepNodes⟩ ← observed (keepFunction.typedBody.nodes = keepShape.nodeList) "keep nodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let ⟨useNodes⟩ ← observed (useFunction.typedBody.nodes = useShape.nodeList) "use nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1024 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          have header := checkedHeader checked member candidateMember accepted
          have ledger := SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
            (checkProgram_success_signature_formation checked) candidateMember accepted
          simp only [functions,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl
          · have same : candidate = keepSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans keepDeclaration)
            subst candidate
            exact keepShape.statementTyping program.signatures header
          · have same : candidate = makeSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans makeDeclaration)
            subst candidate
            exact makeShape.statementTyping program.signatures (by simp [signatures]) (by simp [traits]) ledger
          · have same : candidate = useSignature := eq_of_mem_of_nodup_map
              (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
              (by simp [signatures]) (identity.symm.trans useDeclaration)
            subst candidate
            exact useShape.statementTyping program.signatures header (fun _ binders => ⟨binders,.builtin .word⟩)
        methods := by
          intro actual _member implementation method trait member methodMember lookup accepted
          simp only [implementations,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · simp only [markMethods,List.not_mem_nil] at methodMember
          · exact methodShape.statementTyping methodMember lookup accepted }
      return {
        wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        program := program
        checked := checked
        mark := mark
        coercion := coercion
        traits := traits
        markImplementation := markImplementation
        markMethods := markMethods
        implementation := implementation
        implementations := implementations
        methodShape := methodShape
        parameter := parameter
        keepFunction := keepFunction
        keepSignature := keepSignature
        makeFunction := makeFunction
        makeSignature := makeSignature
        useFunction := useFunction
        useSignature := useSignature
        functions := functions
        signatures := signatures
        keepDeclaration := keepDeclaration
        makeDeclaration := makeDeclaration
        useDeclaration := useDeclaration
        keepShape := keepShape
        makeShape := makeShape
        useShape := useShape
        keepNodes := keepNodes
        makeNodes := makeNodes
        useNodes := useNodes
      }
    | _,_,_,_ => throw (IO.userError "coercion original declarations")

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreCoercionPublic
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
    SourceCompiler.Seed.declaration checked.useSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1024, compilationFuel := 1000, specializationBudget := 256}
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
  member : row ∈ fixture.recipe.compiled.indexed.base.plan.specializations
  origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram row
  sourceOwner : row.function.typedBody.owner = signature.id
  scalarRange : row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true
  keyOwner : row.key.declaration = signature.id
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  index : Nat
  named : SourceCoreGeneralFunctions.Function
  cached : fixture.recipe.compiled.indexed.base.functions[index]? = some named
  same : named.specialized = row

def ObservedRow.global {fixture signature} (observed : ObservedRow fixture signature) : SourceCoreCalls.Signature :=
  observed.named.signature

theorem ObservedRow.globalKey {fixture signature} (observed : ObservedRow fixture signature) :
    observed.global.key = observed.row.key :=
  (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key fixture.recipe.compiled observed.cached).trans
    (congrArg (·.key) observed.same)

theorem ObservedRow.slot {fixture signature} (observed : ObservedRow fixture signature) :
    CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals observed.index observed.global :=
  CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot fixture.recipe.compiled observed.cached

theorem ObservedRow.target {fixture signature} (observed : ObservedRow fixture signature) :
    SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok observed.row.key := by
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram
      observed.named.specialized := observed.same.symm ▸ observed.origin
  have target := CallableIndexedOwnedPreparedOrdinaryCachedInputs.retained_target
    fixture.recipe.compiled fixture.source_wellFormed observed.cached origin
  rw [observed.same] at target
  exact target.trans (congrArg Except.ok observed.globalKey)

structure ObservedRoot (fixture : CompiledFixture) (signature : ProgramFunctionSignature) extends ObservedRow fixture signature where
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeOrigin (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram row)) := do
  match accepted : SourceSpecializationWorklist.resolveRequest fixture.recipe.compiled.sourceProgram
      ⟨row.declaration, row.parameterSubstitution⟩ with
  | .error error => throw (IO.userError (reprStr error))
  | .ok original =>
    let ⟨same⟩ ← observed ((original == row) = true) "actual final row specialization"
    have equal : original = row := eq_of_beq same
    return ⟨equal ▸ RecursiveNamedPublicSpecializationMeaning.resolve_origin accepted⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) (arguments : List TypeSystem.Ty) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.indexed.base.plan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id ∧ row.key.arguments = arguments)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨origin⟩ ← observeOrigin fixture row
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨scalarRange⟩ ← observed (row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true) "generic complete raw range"
    let ⟨keyOwner⟩ ← observed (row.key.declaration = signature.id) "generic row key owner"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    match cached : fixture.recipe.compiled.indexed.base.functions.zipIdx.find?
        (fun item => item.1.specialized == row) with
    | none => throw (IO.userError "actual cached declaration missing")
    | some (named, index) =>
      have same : named.specialized = row := eq_of_beq (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => item.1.specialized == row) cached)
      return {
        origin := origin
        named := named
        cached := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some cached)
        same := same
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
        index := index }


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

theorem ObservedRow.eligible {fixture signature} (observed : ObservedRow fixture signature) :
    CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled observed.row := by
  refine ⟨observed.origin, ?_, observed.ordinary, observed.inputsOrdinary⟩
  intro parameter replacement member
  have scalar := of_decide_eq_true (List.all_eq_true.mp observed.scalarRange (parameter, replacement) member)
  rcases scalar with rfl | rfl
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩

/-- Select the same issued packet from the complete eligible ordinary catalog. -/
theorem ObservedRow.issue_at {fixture signature} (observed : ObservedRow fixture signature)
    (catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.HasRow packet catalog.rows ∧
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  have eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled
      observed.named.specialized := observed.same.symm ▸ observed.eligible
  obtain ⟨input, packet, retained, rowEq, indexEq, namedEq⟩ := catalog.packet_at observed.cached eligible
  have sameRow : input.row = observed.row := rowEq.trans observed.same
  refine ⟨input, sameRow, packet, retained, ?_⟩
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  let reindexed : ActualHeader fixture observed.row := sameRow ▸ actual
  have transport : ∀ {left right : SourceSpecialization.SpecializedFunction}
      (same : left = right) (header : ActualHeader fixture left),
      (same ▸ header).header = header.header := by
    intro left right same header
    cases same
    rfl
  have aligned : reindexed.header = packet.header := transport sameRow actual
  refine ⟨reindexed, aligned, ?_, ?_⟩
  · rw [aligned]
    exact packet.aligned.slot.trans indexEq
  · rw [aligned]
    exact congrArg (·.signature) (packet.aligned.named.trans namedEq)

theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled
    fixture.recipe.compiled fixture.source_wellFormed
  obtain ⟨input, same, packet, _retained, actual, aligned, slot, signature⟩ := observed.issue_at catalog
  exact ⟨input, same, packet, actual, aligned, slot, signature⟩

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

def closureType (type : TypeSystem.Ty) : TypeSystem.Ty := .function .unit type

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 102400
  inputValidationFuel := 1024
  outputValidationFuel := 1024 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its function handle is obtained from the actual public export. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 102400 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.bool true] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle
  handleType : handle.sourceType = closureType .word

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 102400 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.bool true] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          if handleType : handle.sourceType = closureType .word then
            return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
              checkpoint, started, completion, result ▸ executed.property, handle, returned, handleType⟩
          else throw (IO.userError "initial public handle type")
        | _ => throw (IO.userError "initial function export missing")

structure SelectedIdentityShape (function : CheckedFunction) (type : TypeSystem.Ty) where
  binder : TypedBinder
  read : Read function.typedBody binder type
  statement : StatementNode
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono type
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = type

def SelectedIdentityShape.nodeList {function type} (shape : SelectedIdentityShape function type) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

def observeSelectedIdentity (function : CheckedFunction) (type : TypeSystem.Ty) : IO (SelectedIdentityShape function type) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity binder")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "identity nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder node type
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "identity inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono type) "identity binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "identity binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "identity roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "identity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "identity statementType"
  return {binder, read, statement, inputs, binderScheme, binderRequirements, roots, statementFound, statementForm, statementType}

private structure CheckedSourceAdmission (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) : Prop where
  admission : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
    compiled named source statements expected []
  accepted : CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource
    compiled named source statements expected [] 64 = some ⟨admission⟩

private def observeSourceAdmission (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    IO (PLift (CheckedSourceAdmission compiled named source statements expected)) := do
  match accepted : CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource
      compiled named source statements expected [] 64 with
  | none => throw (IO.userError "actual named Source admission failed")
  | some receipt => return ⟨⟨receipt.down, accepted⟩⟩

private structure CheckedSourceMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) : Prop where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite [])
  accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite []) = some ⟨metadata⟩

private def observeSourceMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    IO (PLift (CheckedSourceMetadata compiled named source)) := do
  match accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite []) with
  | none => throw (IO.userError "actual keep expression metadata rejected")
  | some receipt => pure ⟨⟨receipt.down, accepted⟩⟩

structure ObservedProgram (fixture : CompiledFixture) where
  makeRow : ObservedRoot fixture fixture.makeSignature
  useRow : ObservedRoot fixture fixture.useSignature
  keepRow : ObservedRow fixture fixture.keepSignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature fixture.keepSignature fixture.parameter fixture.mark fixture.coercion
  useShape : UseShape useRow.row.function fixture.useSignature .word
  keepShape : SelectedIdentityShape keepRow.row.function .bool
  useAdmission : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
    fixture.recipe.compiled useRow.named useRow.row.function.typedBody [useShape.body.statement.id] .word []
  useAdmissionAccepted : CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource fixture.recipe.compiled
    useRow.named useRow.row.function.typedBody [useShape.body.statement.id] .word [] 64 = some ⟨useAdmission⟩
  keepMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed keepRow.named keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite [])
  keepMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed keepRow.named keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite []) = some ⟨keepMetadata⟩
  makeInputScheme : makeShape.binder.scheme = .mono .bool
  useInputScheme : useShape.body.binder.scheme = .mono (closureType .word)
  makeNodes : makeRow.row.function.typedBody.nodes = makeShape.nodeList
  useNodes : useRow.row.function.typedBody.nodes = useShape.nodeList
  keepNodes : keepRow.row.function.typedBody.nodes = keepShape.nodeList
  makeResultType : makeRow.row.function.inferredBodyType = closureType .word
  useResultType : useRow.row.function.inferredBodyType = .word
  keepResultType : keepRow.row.function.inferredBodyType = .bool
  makeKey : makeRow.row.key = ⟨fixture.makeSignature.id, []⟩
  useKey : useRow.row.key = ⟨fixture.useSignature.id, []⟩
  keepKey : keepRow.row.key = ⟨fixture.keepSignature.id, [.bool]⟩
  keepInstantiation : CallableNamedCanonicalOrder.retainedInstantiation keepRow.row =
    ⟨fixture.keepSignature.id, [(fixture.parameter, .bool)], .function .bool .bool,
      [predicate (.declaration fixture.mark.id) .bool], fixture.keepSignature.parameterComptime, fixture.keepSignature.returnComptime⟩
  makeKeepInstantiation : makeShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keepRow.row
  ordinarySlotsDistinct : [makeRow.index, useRow.index, keepRow.index].Nodup
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 4
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [makeRow.row.key, useRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let makeRow ← observeRootRow fixture fixture.makeSignature
  let useRow ← observeRootRow fixture fixture.useSignature
  let keepRow ← observeRow fixture fixture.keepSignature [.bool]
  let makeShape ← observeFactory makeRow.row.function fixture.makeSignature fixture.keepSignature fixture.parameter fixture.mark fixture.coercion
  let useShape ← observeUse useRow.row.function fixture.useSignature .word
  let keepShape ← observeSelectedIdentity keepRow.row.function .bool
  let ⟨useChecked⟩ ← observeSourceAdmission fixture.recipe.compiled useRow.named
    useRow.row.function.typedBody [useShape.body.statement.id] .word
  let useAdmission := useChecked.admission
  let useAdmissionAccepted := useChecked.accepted
  let ⟨keepChecked⟩ ← observeSourceMetadata fixture.recipe.compiled keepRow.named keepRow.row.function.typedBody
  let keepMetadata := keepChecked.metadata
  let keepMetadataAccepted := keepChecked.accepted
  let ⟨makeInputScheme⟩ ← observed (makeShape.binder.scheme = .mono .bool) "actual coercion fixture makeInputScheme"
  let ⟨useInputScheme⟩ ← observed (useShape.body.binder.scheme = .mono (closureType .word)) "actual coercion fixture useInputScheme"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = makeShape.nodeList) "actual coercion fixture makeNodes"
  let ⟨useNodes⟩ ← observed (useRow.row.function.typedBody.nodes = useShape.nodeList) "actual coercion fixture useNodes"
  let ⟨keepNodes⟩ ← observed (keepRow.row.function.typedBody.nodes = keepShape.nodeList) "actual coercion fixture keepNodes"
  let ⟨makeResultType⟩ ← observed (makeRow.row.function.inferredBodyType = closureType .word) "actual coercion fixture makeResultType"
  let ⟨useResultType⟩ ← observed (useRow.row.function.inferredBodyType = .word) "actual coercion fixture useResultType"
  let ⟨keepResultType⟩ ← observed (keepRow.row.function.inferredBodyType = .bool) "actual coercion fixture keepResultType"
  let ⟨makeKey⟩ ← observed (makeRow.row.key = ⟨fixture.makeSignature.id, []⟩) "actual coercion fixture makeKey"
  let ⟨useKey⟩ ← observed (useRow.row.key = ⟨fixture.useSignature.id, []⟩) "actual coercion fixture useKey"
  let ⟨keepKey⟩ ← observed (keepRow.row.key = ⟨fixture.keepSignature.id, [.bool]⟩) "actual coercion fixture keepKey"
  let ⟨keepInstantiation⟩ ← observed (CallableNamedCanonicalOrder.retainedInstantiation keepRow.row =
    ⟨fixture.keepSignature.id, [(fixture.parameter, .bool)], .function .bool .bool,
      [predicate (.declaration fixture.mark.id) .bool], fixture.keepSignature.parameterComptime, fixture.keepSignature.returnComptime⟩) "actual coercion fixture keepInstantiation"
  let ⟨makeKeepInstantiation⟩ ← observed (makeShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keepRow.row) "actual coercion fixture makeKeepInstantiation"
  let ⟨ordinarySlotsDistinct⟩ ← observed ([makeRow.index, useRow.index, keepRow.index].Nodup) "actual coercion fixture ordinarySlotsDistinct"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 4) "actual coercion fixture globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [makeRow.row.key, useRow.row.key]) "actual coercion fixture entryKeys"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual coercion fixture noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual coercion fixture profile"
  return {makeRow, useRow, keepRow, makeShape, useShape, keepShape, useAdmission, useAdmissionAccepted, keepMetadata, keepMetadataAccepted, makeInputScheme, useInputScheme, makeNodes, useNodes, keepNodes, makeResultType, useResultType, keepResultType, makeKey, useKey, keepKey, keepInstantiation, makeKeepInstantiation, ordinarySlotsDistinct, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicCatalog
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ClosedImplementation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters = []
  subject : implementation.head.subject = .word ∨ implementation.head.subject = .bool
  arguments : implementation.head.arguments = [] ∨ implementation.head.arguments = [.word]
  predicates : implementation.wherePredicates = []
  methods : ∀ method, method ∈ implementation.methods → method.wherePredicates = []

theorem ClosedImplementation.formed {implementation : ProgramImplementationSignature}
    (closed : ClosedImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨closed.parameters ▸ List.nodup_nil, ?_, ?_, ?_⟩
  · intro metavariable
    rcases closed.arguments with args | args <;> rcases closed.subject with scalar | scalar <;>
      simp [TypedTraitResolution.VariableOccursInPredicate, scalar, args, TypeSystem.Ty.word, TypeSystem.Ty.bool, TypeSystem.Ty.freeVariables]
  · intro parameter occurs
    have noWord : ¬ TypeSystem.TypeParameterOccurs parameter .word := by intro h; cases h
    have noBool : ¬ TypeSystem.TypeParameterOccurs parameter .bool := by intro h; cases h
    rcases closed.arguments with args | args <;> rcases closed.subject with scalar | scalar <;>
      simp [TypedTraitResolution.ParameterOccursInPredicate, scalar, args, noWord, noBool] at occurs
  · intro predicate predicateMember parameter _occurs
    rw [closed.methods method member] at predicateMember
    cases predicateMember

def observeClosedImplementation (implementation : ProgramImplementationSignature) :
    IO (PLift (ClosedImplementation implementation)) := do
  let ⟨parameters⟩ ← observed (implementation.parameters = []) "method implementation parameters"
  let ⟨subject⟩ ← observed (implementation.head.subject = .word ∨ implementation.head.subject = .bool) "method implementation subject"
  let ⟨arguments⟩ ← observed (implementation.head.arguments = [] ∨ implementation.head.arguments = [.word]) "method implementation head arguments"
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
    IO (PLift (CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)) := do
  let ⟨closed⟩ ← observeClosedImplementations fixture.recipe.compiled.sourceProgram.signatures.implementations
  let ⟨traits⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.traits.all
    (fun trait => decide (trait.wherePredicates = [])) = true) "method trait predicates"
  let some ⟨shapes⟩ := CallableCoercionSourceShapeTable.validate fixture.recipe.compiled.sourceProgram fixture.recipe.compiled.indexed.base.plan.specializations
    | throw (IO.userError "actual coercion method source shapes")
  return ⟨{
    shapes := shapes
    parameters := fun implementation member _method _methodMember => (closed implementation member).parameters
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

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicFactorySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

/-- The executable certificate retains the actual cached factory row. Its
inner call still carries the original ordered evidence and coercion path. -/
structure ObservedFactory (fixture : CompiledFixture) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) where
  certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled row.named
  accepted : CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory
    fixture.recipe.compiled row.named = some certificate

def observeFactorySupport (fixture : CompiledFixture) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) : IO (ObservedFactory fixture row) := do
  match accepted : CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory
      fixture.recipe.compiled row.named with
  | none => throw (IO.userError "actual cached factory source admission failed")
  | some certificate => return ⟨certificate, accepted⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  make : ObservedFactory fixture observed.makeRow.toObservedRow

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.makeRow.toObservedRow⟩

theorem ActualHeader.factory_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {mark coercion : ProgramTraitSignature} (_shape : FactoryShape row.row.function signature generic parameter mark coercion)
    (extra : ObservedFactory fixture row) (actual : ActualHeader fixture row.row)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {stages : Staging.Recursive.Registry} :
    ∃ terminal : Terminal actual.header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) actual.header terminal) := by
  exact CallableIndexedOwnedPreparedNamedFactoryAdmission.of_actual actual.prepared actual.aligned
    row.cached row.same extra.certificate fixture.recipePrepared actual.diagnostic
    fixture.source_wellFormed observed.profile observed.makeRow.entryMember

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  makeSame : makeInput.row = observed.makeRow.row
  makePacket : Issued makeInput
  makeRetained : Inventory.HasRow makePacket catalog.rows
  makeHeader : ActualHeader fixture observed.makeRow.row
  makeAligned : makeHeader.header = makePacket.header
  makeSlot : makeHeader.header.slot = observed.makeRow.index
  makeSignature : makeHeader.header.named.signature = observed.makeRow.global
  useInput : Input fixture.recipe.compiled
  useSame : useInput.row = observed.useRow.row
  usePacket : Issued useInput
  useRetained : Inventory.HasRow usePacket catalog.rows
  useHeader : ActualHeader fixture observed.useRow.row
  useAligned : useHeader.header = usePacket.header
  useSlot : useHeader.header.slot = observed.useRow.index
  useSignature : useHeader.header.named.signature = observed.useRow.global
  keepInput : Input fixture.recipe.compiled
  keepSame : keepInput.row = observed.keepRow.row
  keepPacket : Issued keepInput
  keepRetained : Inventory.HasRow keepPacket catalog.rows
  keepHeader : ActualHeader fixture observed.keepRow.row
  keepAligned : keepHeader.header = keepPacket.header
  keepSlot : keepHeader.header.slot = observed.keepRow.index
  keepSignature : keepHeader.header.named.signature = observed.keepRow.global

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.makeInput, given.useInput, given.keepInput] :=
  .cons given.makePacket (.cons given.usePacket (.cons given.keepPacket .nil))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled fixture.recipe.compiled fixture.source_wellFormed
  obtain ⟨makeInput, makeSame, makePacket, makeRetained, makeHeader, makeAligned, makeSlot, makeSignature⟩ := observed.makeRow.issue_at catalog
  obtain ⟨useInput, useSame, usePacket, useRetained, useHeader, useAligned, useSlot, useSignature⟩ := observed.useRow.issue_at catalog
  obtain ⟨keepInput, keepSame, keepPacket, keepRetained, keepHeader, keepAligned, keepSlot, keepSignature⟩ := observed.keepRow.issue_at catalog
  exact ⟨{catalog, makeInput, makeSame, makePacket, makeRetained, makeHeader, makeAligned, makeSlot, makeSignature, useInput, useSame, usePacket, useRetained, useHeader, useAligned, useSlot, useSignature, keepInput, keepSame, keepPacket, keepRetained, keepHeader, keepAligned, keepSlot, keepSignature}⟩

theorem OrdinaryInventory.make_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeHeader.header ∈ headers given.rows := by
  rw [given.makeAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.use_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useHeader.header ∈ headers given.rows := by
  rw [given.useAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.keep_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.keepHeader.header ∈ headers given.rows := by
  rw [given.keepAligned]
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

/-- Both public entries have genuine ordinary Source headers. The separate
physical cache also retains the actual coercion method. -/
theorem OrdinaryInventory.public_coverage {fixture observed}
    (given : OrdinaryInventory fixture observed) :
    RecursiveNamedPublicRootCoverage.Coverage
      (compiled := fixture.recipe.compiled)
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (headers given.rows) := by
  intro entry member named slot found
  have entryKey : entry.key ∈ [observed.makeRow.row.key, observed.useRow.row.key] := by
    rw [← observed.entryKeys]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have namedKey : named.signature.key = entry.key := of_decide_eq_true (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = entry.key)) found)
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled
    (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryKey
  rcases entryKey with same | same
  · have slots := observed.makeRow.global_slot selected (namedKey.trans same)
    exact ⟨given.makeHeader.header, given.make_member, given.makeSlot.trans slots.2.symm⟩
  · have slots := observed.useRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useHeader.header, given.use_member, given.useSlot.trans slots.2.symm⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
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

theorem ObservedProgram.keep_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.makeShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.makeShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.makeKeepInstantiation]
    exact retained_ordered observed.keepRow.target observed.keepRow.record

section Use
variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : UseShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem UseShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.body.read.node ∨ node = shape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [Tests.SourceCoreMethodClosure.UseShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem UseShape.policy_metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact .inl shape.body.read.requirements
    · exact .inl shape.value.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact shape.body.read.coercions
    · exact shape.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · rw [shape.body.read.form] at form; cases form
    · rw [shape.form] at form
      have same : shape.metadata = metadata := CallResolution.indirect.inj (ExpressionForm.call.inj form).2.2
      rw [← same, shape.application]
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem UseShape.syntax : GeneralSyntax function.typedBody shape.value.node.id (fun _ => False) := by
  refine .call shape.value.found shape.form (.leaf (.read shape.body.read.found shape.body.read.form)) ?_
  intro id member
  cases member
end Use
section Identity
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedIdentityShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedIdentityShape.expression {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) : node = shape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedIdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem SelectedIdentityShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rw [shape.expression nodes found]
    exact .inl shape.read.requirements
  · intro id _ node found
    rw [shape.expression nodes found]
    exact shape.read.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [shape.expression nodes found, shape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem SelectedIdentityShape.syntax : GeneralSyntax function.typedBody shape.read.node.id (fun _ => False) :=
  .leaf (.read shape.read.found shape.read.form)
end Identity
end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicFactoryMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)

variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {mark coercion : ProgramTraitSignature}
  (shape : FactoryShape function signature generic parameter mark coercion)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem FactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.read.node ∨ node = shape.call.callee.node ∨ node = shape.call.node ∨
      node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
/-- Only the actual uncoerced argument grammar is admitted by this profile.
The original constrained call remains outside that grammar. -/
theorem FactoryShape.native_metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    NativeMetadataFor fixture.recipe.compiled.indexed named function.typedBody (fun _ => False) := by
  constructor
  · intro id tree node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact .inl shape.read.requirements
    · exact .inl shape.call.callee.requirements
    · exact False.elim (tree.direct_site found shape.call.form)
    · exact .inl shape.expression.requirements
  · intro id tree node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.read.coercions
    · exact shape.call.callee.coercions
    · exact False.elim (tree.direct_site found shape.call.form)
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · rw [shape.read.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
    · rw [shape.lambda] at form; cases form
  · intro id tree node found callee ids instantiation form
    exact False.elim (tree.direct_site found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem FactoryShape.children : ∀ id ∈ [shape.read.node.id],
    GeneralSyntax function.typedBody id (fun _ => False) := by
  intro id member
  have same := List.mem_singleton.mp member
  subst id
  exact .leaf (.read shape.read.found shape.read.form)

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicMethodSyntax
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

variable {function : CheckedFunction} {signature : ProgramFunctionSignature}
  (shape : MethodShape function signature) (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem MethodShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.read.node ∨ node = shape.first.node ∨ node = shape.second.node ∨ node = shape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [MethodShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem MethodShape.primitive_source :
    CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.PrimitiveSource function.typedBody := by
  intro id node found
  rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
  · exact .inl ⟨_, _, shape.read.form⟩
  · exact .inr (.inl ⟨_, _, shape.first.form⟩)
  · exact .inr (.inl ⟨_, _, shape.second.form⟩)
  · exact .inr (.inr ⟨_, _, _, shape.conditional⟩)

include nodes in
theorem MethodShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody (fun _ => False) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · exact .inl shape.read.requirements
    · exact .inr (.inl ⟨_, _, shape.first.form⟩)
    · exact .inr (.inl ⟨_, _, shape.second.form⟩)
    · exact .inl shape.value.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · exact shape.read.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound shape.first.accepted).coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound shape.second.accepted).coercions
    · exact shape.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · rw [shape.read.form] at form; cases form
    · rw [shape.first.form] at form; cases form
    · rw [shape.second.form] at form; cases form
    · rw [shape.conditional] at form; cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem MethodShape.syntax : GeneralSyntax function.typedBody shape.value.node.id (fun _ => False) := by
  refine .conditional shape.value.found shape.conditional (.leaf (.read shape.read.found shape.read.form)) ?_ ?_
  · exact .leaf (.literal shape.first.found (shape.first.form ▸ .integer _ _))
  · exact .leaf (.literal shape.second.found (shape.second.form ▸ .integer _ _))

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicMethodSupport
/-! Actual operator selections retain the complete specialized method source and
its synthetic signature. The finite cached table supplies scoped syntax without
erasing the implementation substitution; SourceAt supplies independent typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure MethodSource (fixture : CompiledFixture) (source : TypedSource) (resultType : TypeSystem.Ty) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  shape : MethodShape function signature
  sameSource : source = function.typedBody
  nodes : function.typedBody.nodes = shape.nodeList
  result : resultType = .word

private def observeMethodSource (fixture : CompiledFixture) (method : ExecutableImplMethods.CheckedMethod) :
    IO (MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) := do
  let function := method.specialized.function
  let signature := method.synthetic
  let shape ← observeMethod function signature
  let ⟨result⟩ ← observed (function.inferredBodyType = .word) "coercion method result"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "actual specialized coercion method nodes"
  return ⟨function, signature, shape, rfl, nodes, result⟩

private def MethodRowCase (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Nonempty (MethodSource fixture named.specialized.function.typedBody named.specialized.function.inferredBodyType)

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodRowCase fixture named

private def observeSelectedMethod (fixture : CompiledFixture)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode) (step : CoercionStep) :
    IO ExecutableImplMethods.CheckedMethod := do
  let available ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      fixture.recipe.compiled.sourceProgram caller.key caller.assumptions with
    | .ok available => pure available
    | .error error => throw (IO.userError (reprStr error))
  match SourceCompilationPlan.checkedCoercionMethod fixture.recipe.compiled.sourceProgram caller node available step with
  | .ok method => pure method
  | .error error => throw (IO.userError (reprStr error))

private def observeMethodBodyList (fixture : CompiledFixture)
    (method : ExecutableImplMethods.CheckedMethod)
    (methodSource : MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) :
    (named : List SourceCoreGeneralFunctions.Function) → IO (PLift (∀ row ∈ named, MethodRowCase fixture row))
  | [] => pure ⟨by intro row member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (do
      if nonMethod : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
          (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        return ⟨Or.inl (by intro definition member; exact of_decide_eq_true (List.all_eq_true.mp nonMethod definition member))⟩
      else if same : (first.specialized == method.specialized) = true then
        have equal : first.specialized = method.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨methodSource⟩)⟩
      else throw (IO.userError "actual cached method specialization missing") : IO (PLift (MethodRowCase fixture first)))
    let ⟨tail⟩ ← observeMethodBodyList fixture method methodSource rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail row member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let program ← observeProgram fixture
  let method ← observeSelectedMethod fixture program.makeRow.row program.makeShape.call.node program.makeShape.call.step
  let methodSource ← observeMethodSource fixture method
  let ⟨bodies⟩ ← observeMethodBodyList fixture method methodSource fixture.recipe.compiled.indexed.base.functions
  return ⟨⟨bodies⟩⟩

theorem MethodBodies.selected {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) :
    Nonempty (MethodSource fixture principal.sourceBody.source principal.sourceBody.resultType) := by
  have member := List.mem_of_getElem? principal.cached.selected
  rcases bodies.bodies principal.named member with excluded | shape
  · obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
    cases instantiated with
    | intro _ _ _ _ definitionMember _ _ _ _ source _ _ =>
      have selectedOwner : principal.sourceBody.source.owner = definition.body.source.owner := by
        rw [source]
        rfl
      have namedOwner : principal.named.specialized.function.typedBody.owner = principal.sourceBody.source.owner := by
        rw [principal.cached.same]
        rfl
      exact False.elim (excluded definition definitionMember (namedOwner.trans selectedOwner))
  · simpa only [principal.cached.same, CallableIndexedOwnedMethodPrincipal.Principal.sourceBody,
      CallableCoercionMethodInstantiation.bodyInstance] using shape

/-- The original selected method table has only reads, literals and a conditional. -/
theorem MethodBodies.no_lambda {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨original⟩ := bodies.selected principal
  rw [original.sameSource] at found
  rcases original.shape.primitive_source original.nodes id node found with
    ⟨name, resolution, read⟩ | ⟨spelling, resolution, read⟩ | ⟨condition, first, second, read⟩ <;>
    rw [read] at form <;> cases form

/-- A terminal packet is issued from the selected cached method and its actual
compiler action. The same SourceAt receipt remains available for parameter entry. -/
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
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support principal packet headers stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨original⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = [original.shape.statement.id] := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [original.sameSource, original.shape.roots] at roots
    simpa using roots.symm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal principal.sourceBody.source
      original.shape.value.node.id principal.cached.compilation.statements := by
    have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
        original.function.typedBody original.shape.value.node.id [original.shape.statement.id] :=
      .returning [] original.shape.statementFound original.shape.statementForm
    simpa only [original.sameSource, statements] using originalTerminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal := ⟨sourceAt, _, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  apply CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.of_actual principal packet diagnostic receiver
    fixture.source_wellFormed
  · rw [original.sameSource]
    exact original.shape.primitive_source original.nodes
  · rw [original.sameSource]
    exact original.shape.metadata original.nodes principal.named observed.noLocals
  · change CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      principal.sourceBody.source original.shape.value.node.id (fun _ => False)
    simpa only [original.sameSource] using original.shape.syntax

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicClosureSupport
/-! Actual cached Source graphs identify the factory lambda body. Their
retained ordinary provenance supplies the coerced direct call, its complete
dictionary and actual physical slot; the selected method contains a read, literals and a conditional. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport (PacketFor SupportFor)

private def lambdaNode : Node → Bool
  | .expression node => match node.form with | .lambda .. => true | _ => false
  | _ => false

/-- This finite observation checks every actual cache row, including methods. -/
structure ObservedClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) : Prop where
  checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody)
      else true)) = true

def observeClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (PLift (ObservedClosureSources fixture observed)) := do
  if checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody)
      else true)) = true then
    return ⟨⟨checked⟩⟩
  else throw (IO.userError "actual cached lambda Source attribution")

theorem ObservedClosureSources.selected {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (sources : ObservedClosureSources fixture observed)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named)
    {id node parameters result body}
    (found : ContainsExpression (CallableIndexedNamedGeneration.source named) id node)
    (form : node.form = .lambda parameters result body) :
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody := by
  have row := List.all_eq_true.mp sources.checked named (List.mem_of_getElem? selected)
  have expression := List.all_eq_true.mp row (.expression node) found.1
  simpa only [lambdaNode, form, Bool.true_eq, ↓reduceIte, decide_eq_true_eq] using expression

private theorem factory_lambda_shape {function : CheckedFunction}
    {signature generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {mark coercion : ProgramTraitSignature}
    (shape : FactoryShape function signature generic parameter mark coercion)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [shape.innerReturn.id] := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simp only [FactoryShape.nodeList, List.mem_cons,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] at present
  rcases present with same | same | same | same
  all_goals subst node
  · rw [shape.read.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (bodies : MethodBodies fixture) (given : OrdinaryInventory fixture observed)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = observed.makeRow.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SelectedBody (headers := headers given.rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape observed.makeShape observed.makeNodes found code.sourceForm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source observed.makeShape.call.node.id function.body := by
    rw [sameSource, lambda.2.2]
    exact .returning [] observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source (fun _ => False) := by
    rw [sameSource]
    exact observed.makeShape.native_metadata observed.makeNodes support.caller.named observed.noLocals
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan
        observed.makeShape.call.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers given.rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    change SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      observed.makeShape.call.instantiation = .ok signature.key at target
    change fixture.recipe.compiled.indexed.base.globals[index]? = some signature at global
    rw [observed.makeKeepInstantiation, observed.keepRow.target] at target
    have key := Except.ok.inj target
    obtain ⟨signatureEq, indexEq⟩ := observed.keepRow.global_slot global key.symm
    exact ⟨given.keepHeader.header, given.keep_member,
      given.keepSlot.trans indexEq.symm, given.keepSignature.trans signatureEq.symm⟩
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  apply CallableIndexedOwnedPreparedStagedOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed metadata given.rows checked _ methods
    (signature := fixture.makeSignature)
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
    (by rw [sameSource]; exact observed.makeRow.sourceOwner)
    (fun principal sourceAt diagnostic => bodies.support observed principal sourceAt diagnostic receiver
      (headers := headers given.rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared))
    observed.makeShape.call.node.id terminal
    (by rw [sameSource]; exact observed.makeShape.call.found)
    observed.makeShape.call.form
    (by rw [observed.makeShape.call.coercions]; simp)
    (by rw [observed.makeShape.call.requirements]; simp)
    (by
      intro argument member
      cases List.mem_singleton.mp member
      rw [sameSource]
      exact .leaf (.read observed.makeShape.read.found observed.makeShape.read.form))
    (by simp only [observed.noLocals, List.find?_nil])
    (by rw [support.compilation]; exact observed.keep_supported)
    covered _ (.anonymous selected)
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

/-- Actual retained compiler provenance identifies the factory body. The packet
keeps the original direct-call node, complete evidence and output coercion. -/
theorem closure_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (given : OrdinaryInventory fixture observed)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    {registry : SourceCoreRawMetadata.Registry} {keys}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers given.rows) keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : PacketFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SupportFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet) := by
  rcases association with ⟨association, _slots⟩
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source] at found
    have original := sources.selected support.caller.selected (lookupExpression?_sound found) code.sourceForm
    obtain ⟨⟨packet, supported⟩⟩ := factory_packet observed bodies given stagePrepared receiver methods
      code support provenance (support.source.trans original)
    exact ⟨⟨.terminal packet, supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    exact False.elim (bodies.no_lambda support.principal found code.sourceForm)

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics

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

/-- Every use is an original compiled Source indirect call, reached through a
public named entry with the previously exported handle as its actual input. -/
structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow.toObservedRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.bool false]
  secondType : second.handle.sourceType = closureType .word
  firstRead : ObservedCall second.completion.session observed.useRow.row.key [.function first.handle]
  firstValue : firstRead.completion.value = .word (Core.Word.ofNatModulo 41)
  third : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.bool false]
  thirdType : third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedCall third.completion.session observed.useRow.row.key [.function second.handle]
  secondValue : secondRead.completion.value = .word (Core.Word.ofNatModulo 7)
  repeatedRead : ObservedCall secondRead.completion.session observed.useRow.row.key [.function first.handle]
  repeatedValue : repeatedRead.completion.value = .word (Core.Word.ofNatModulo 41)
  thirdRead : ObservedCall repeatedRead.completion.session observed.useRow.row.key [.function third.handle]
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 7)
  heapSizes : [first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [5,11,17,29,35,47,59,71]

def observeSequence (fixture : CompiledFixture) (program : ObservedProgram fixture) :
    IO (ObservedSequence fixture program) := do
  let first ← observePublicRun fixture program.makeRow.toObservedRow
  let second ← observeFunctionCall first.completion.session program.makeRow.row.key [.bool false]
  let ⟨secondType⟩ ← observed (second.handle.sourceType = closureType .word) "second public handle type"
  let firstRead ← observeCall second.completion.session program.useRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← observed (firstRead.completion.value = .word (Core.Word.ofNatModulo 41)) "first compiled indirect output"
  let third ← observeFunctionCall firstRead.completion.session program.makeRow.row.key [.bool false]
  let ⟨thirdType⟩ ← observed (third.handle.sourceType = closureType .word) "third public handle type"
  let ⟨firstSecond⟩ ← observed (first.handle ≠ second.handle) "first/second handles distinct"
  let ⟨firstThird⟩ ← observed (first.handle ≠ third.handle) "first/third handles distinct"
  let ⟨secondThird⟩ ← observed (second.handle ≠ third.handle) "second/third handles distinct"
  let secondRead ← observeCall third.completion.session program.useRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← observed (secondRead.completion.value = .word (Core.Word.ofNatModulo 7)) "second compiled indirect output"
  let repeatedRead ← observeCall secondRead.completion.session program.useRow.row.key [.function first.handle]
  let ⟨repeatedValue⟩ ← observed (repeatedRead.completion.value = .word (Core.Word.ofNatModulo 41)) "retained first compiled indirect output"
  let thirdRead ← observeCall repeatedRead.completion.session program.useRow.row.key [.function third.handle]
  let ⟨thirdValue⟩ ← observed (thirdRead.completion.value = .word (Core.Word.ofNatModulo 7)) "third compiled indirect output"
  let ⟨heapSizes⟩ ← observed ([first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [5,11,17,29,35,47,59,71]) "exact seven-session heap sequence"
  return {first, second, secondType, firstRead, firstValue, third, thirdType, firstSecond, firstThird, secondThird, secondRead, secondValue, repeatedRead, repeatedValue, thirdRead, thirdValue, heapSizes}
end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicCommon
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
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
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.makeRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def OrdinaryInventory.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions (headers inventory.rows)
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
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general observed.profile origin)

abbrev RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) :=
  RecursiveNamedPublicPhysicalSessionState.State inventory.rows inventory.makeHeader.header
    receiver.completion observed.profile fixture.recipe publicSession entries

abbrev SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall inventory.makeHeader.header header
    invocation before arguments outcome after

theorem bool_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (value : Bool) :
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
  exact same ▸ SourceCoreIndexedSession.SimplePublic.bool value

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicKeepCompilerSupport
/-! The actual compiled keep body supplies its statement tree. Only original
expression metadata and its selected return occurrence are supplied here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

theorem ActualHeader.keep_compiler_admission (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have indexEq := (observed.keepRow.prepared_slot actual.prepared).2
  have selected : fixture.recipe.compiled.indexed.base.functions[observed.keepRow.index]? =
      some actual.prepared.named := indexEq ▸ actual.prepared.selected
  have namedEq : actual.prepared.named = observed.keepRow.named :=
    Option.some.inj (selected.symm.trans observed.keepRow.cached)
  have bodyEq : actual.header.function.body = [observed.keepShape.statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [observed.keepShape.statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, observed.keepShape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have found : actual.header.function.source.lookupStatement? observed.keepShape.statement.id =
      some observed.keepShape.statement := by
    rw [actual.source]
    exact observed.keepShape.statementFound
  have child : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      actual.header.function.source observed.keepShape.read.node.id
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) := by
    rw [actual.source]
    exact .leaf (.read observed.keepShape.read.found observed.keepShape.read.form)
  exact AcceptedNamedBodyAdmission.of_returning actual.prepared actual.aligned metadata
    bodyEq found observed.keepShape.statementForm child fixture.source_wellFormed

/-- The original cache identity transports the compiler-derived admission to
its exact retained function. No program certificate is needed for this proof. -/
theorem ObservedProgram.keep_source_admission (observed : ObservedProgram fixture)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.keepRow.named observed.keepRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements
        observed.keepRow.named.specialized.function.typedBody)
      observed.keepRow.named.specialized.function.inferredBodyType directRows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.keepHeader.prepared
    inventory.keepHeader.aligned observed.keepRow.cached observed.keepRow.same
    (inventory.keepHeader.keep_compiler_admission observed metadata)

include rows receiver methods in
theorem ActualHeader.keep_compiler_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual actual.prepared actual.aligned rows
    (.empty _) (actual.keep_compiler_admission observed observed.keepMetadata)
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed
    (CallableMethodBodyCoherence.of_checked (by rw [fixture.sameProgram]; exact fixture.checked))
    (by rw [fixture.sameProgram]; exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked)
    methods observed.makeRow.entryMember (actualStagePrepared fixture)

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicMakeStep
/-! Actual factory calls append their freshly exported closures to the same physical history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.make_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : RetainedState inventory receiver call.completion.session (entries ++ [entry]),
        SourceCall inventory request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  exact RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle program fixture.recipePrepared state call request inputs
    (request.started.simple_registry state.registry simple) descriptor invocation

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicProgramCertificate
/-! The actual keep cache row receives its body from the accepted compiler
receipt. The complementary checker validates every other root and all closures
and methods, then the same full certificate feeds both public issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  pending : AcceptedProgramBodyCompletion.Pending fixture.recipe.compiled observed.keepRow.index
  accepted : AcceptedProgramBodyCompletion.certify fixture.recipe.compiled
    fixture.source_wellFormed observed.keepRow.index 64 = some pending
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨metadata⟩
  rows : ∀ row ∈ pending.table.rows,
    row = observed.makeRow.row ∨ row = observed.useRow.row ∨ row = observed.keepRow.row

/-- The only pending root is filled from the authentic Header compiler action;
all remaining fields are retained from the executed finite checker. -/
def ObservedProgramCertificate.certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled :=
  admission.pending.complete (.scoped (by
    have same : admission.pending.chosen = observed.keepRow.named :=
      Option.some.inj (admission.pending.selected.symm.trans observed.keepRow.cached)
    rw [same]
    exact observed.keep_source_admission admission.metadata))

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : AcceptedProgramBodyCompletion.certify fixture.recipe.compiled
      fixture.source_wellFormed observed.keepRow.index 64 with
  | none => throw (IO.userError "original coercion complementary certification rejected")
  | some pending =>
      match metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
          fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
          (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) with
      | none => throw (IO.userError "original keep expression metadata rejected")
      | some metadata =>
          if rows : pending.table.rows.all (fun row =>
              (row == observed.makeRow.row) || ((row == observed.useRow.row) || (row == observed.keepRow.row))) = true then
            pure ⟨pending, accepted, metadata.down, metadataAccepted, by
              intro row member
              have same := List.all_eq_true.mp rows row member
              simp only [Bool.or_eq_true] at same
              rcases same with same | same | same
              · exact .inl (eq_of_beq same)
              · exact .inr (.inl (eq_of_beq same))
              · exact .inr (.inr (eq_of_beq same))⟩
          else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.useInput, inventory.keepInput] admission.certificate.table.rows := by
  intro row member
  rcases admission.rows row member with rfl | rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeSame⟩
  · exact ⟨inventory.useInput, by simp, inventory.useSame⟩
  · exact ⟨inventory.keepInput, by simp, inventory.keepSame⟩

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.makeRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)

/-- This proof is exercised by the same runtime-produced certificate used by
the seven-call regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
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

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

/-- An actual issued root needs only its selected Header in the local inventory. -/
theorem OrdinaryInventory.selected_row_issued {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (given : OrdinaryInventory fixture observed) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) (header : ActualHeader fixture row.row)
    (member : header.header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows)
    (slot : header.header.slot = row.index)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    (issued : root.Issued fixture.recipe.compiled) (key : root.key = row.row.key) :
    RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows) root header.header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, first, namedKey, rootKey, rest⟩ := shape
  have cached := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some first)
  have atSlot := row.global_slot (CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled cached)
    (namedKey.trans (rootKey.symm.trans key))
  exact RecursiveNamedPublicRootMeaning.selection_at member entryMember
    ⟨named, index, first, namedKey, rootKey, rest⟩ first (slot.trans atSlot.2.symm)

/-- Only the actual first matching public root is selected here. Other public
entries and physical method slots do not require a coverage premise. -/
theorem OrdinaryInventory.selected_row {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (given : OrdinaryInventory fixture observed) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) (header : ActualHeader fixture row.row)
    (member : header.header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows)
    (slot : header.header.slot = row.index)
    (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
    (found : fixture.recipe.roots.find? (fun candidate => decide (candidate.key = row.row.key)) =
      some ((SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared).symm ▸ root)) :
    RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers given.rows) root header.header := by
  have key : root.key = row.row.key := by
    have key := of_decide_eq_true (List.find?_some
      (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (candidate.key = row.row.key)) found)
    exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared).symm root).symm.trans key
  have issued : root.Issued fixture.recipe.compiled := by
    have actual := SourceCoreIndexedSession.Recipe.prepare_roots fixture.recipePrepared
      (List.mem_of_find?_eq_some found)
    cases SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared
    exact actual
  exact given.selected_row_issued row header member slot issued key

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

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, useHeader.header, keepHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have member : header ∈ [makeHeader.header, useHeader.header, keepHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, useHeader.key] at headerKey
    have distinct : observed.makeRow.index ≠ observed.useRow.index := by
      intro equal
      have impossible : 0 = 1 := (List.getElem_inj
        (i := 0) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.makeRow.toObservedRow.keys_ne observed.useRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, keepHeader.key] at headerKey
    have distinct : observed.makeRow.index ≠ observed.keepRow.index := by
      intro equal
      have impossible : 0 = 2 := (List.getElem_inj
        (i := 0) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.makeRow.toObservedRow.keys_ne observed.keepRow distinct) headerKey.symm)

theorem selected_use_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, useHeader.header, keepHeader.header] root header)
    (key : root.key = observed.useRow.row.key) : header = useHeader.header := by
  have member : header ∈ [makeHeader.header, useHeader.header, keepHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, makeHeader.key] at headerKey
    have distinct : observed.useRow.index ≠ observed.makeRow.index := by
      intro equal
      have impossible : 1 = 0 := (List.getElem_inj
        (i := 1) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useRow.toObservedRow.keys_ne observed.makeRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, keepHeader.key] at headerKey
    have distinct : observed.useRow.index ≠ observed.keepRow.index := by
      intro equal
      have impossible : 1 = 2 := (List.getElem_inj
        (i := 1) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useRow.toObservedRow.keys_ne observed.keepRow distinct) headerKey.symm)

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (useHeader : ActualHeader fixture observed.useRow.row)
    (keepHeader : ActualHeader fixture observed.keepRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_make_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, useHeader.header, keepHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root makeHeader useHeader keepHeader request.selected (started_key request)

theorem selected_use_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, useHeader.header, keepHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useRow.row.key arguments fuel world store) : request.header = useHeader.header := by
  subst headers
  exact selected_use_root makeHeader useHeader keepHeader request.selected (started_key request)

end StartedSelection

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.makeInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.make_input_types

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.makeResultType

theorem ActualHeader.make_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.output = Core.CallableContract.functionType .unit .word := by
  have projected := actual.aligned.projection
  rw [actual.make_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.use_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.use_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.types = [closureType .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.use_input_types

theorem ActualHeader.use_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useResultType

theorem ActualHeader.use_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.use_result_type] at projected
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
      [inventory.makeHeader.header, inventory.useHeader.header, inventory.keepHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.makeAligned, inventory.useAligned, inventory.keepAligned]

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    [given.makeInput, given.useInput, given.keepInput].map (fun input => input.prepared.index) =
      [observed.makeRow.index, observed.useRow.index, observed.keepRow.index] := by
  have make : given.makeInput.prepared.index = observed.makeRow.index := by
    have same : given.makeHeader.header.slot = given.makeInput.prepared.index := by
      rw [given.makeAligned]; exact given.makePacket.aligned.slot
    exact same.symm.trans given.makeSlot
  have use : given.useInput.prepared.index = observed.useRow.index := by
    have same : given.useHeader.header.slot = given.useInput.prepared.index := by
      rw [given.useAligned]; exact given.usePacket.aligned.slot
    exact same.symm.trans given.useSlot
  have keep : given.keepInput.prepared.index = observed.keepRow.index := by
    have same : given.keepHeader.header.slot = given.keepInput.prepared.index := by
      rw [given.keepAligned]; exact given.keepPacket.aligned.slot
    exact same.symm.trans given.keepSlot
  simp only [List.map_cons, List.map_nil, make, use, keep]

theorem OrdinaryInventory.distinct {fixture observed} (given : OrdinaryInventory fixture observed) :
    ([given.makeInput, given.useInput, given.keepInput].map (fun input => input.prepared.index)).Nodup := by
  rw [given.indices]
  exact observed.ordinarySlotsDistinct

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicSeed
/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    ObservedFunctionCall first.session observed.makeRow.row.key [.bool true] :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started inventory.rows fixture.recipePrepared
      inventory.makeHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have selected := inventory.selected_row_issued observed.makeRow.toObservedRow
    inventory.makeHeader inventory.make_member inventory.makeSlot
    (SourceCoreIndexedSession.Recipe.prepare_roots prepared (List.mem_of_find?_eq_some started.selected))
    (of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
      decide (candidate.key = observed.makeRow.row.key)) started.selected))
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 102400, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.makeInput, inventory.useInput, inventory.keepInput].map (fun input => input.prepared.index)).Nodup)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (stages : ObservedStages fixture observed.makeRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.makeHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
          ⟨[]⟩ [.bool true] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.makeHeader.header.function.context [.bool true] inventory.makeHeader.header.types := by
    rw [inventory.makeHeader.make_types]
    exact .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool true] [.bool true] :=
    .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function inventory.rows fixture.recipePrepared
      inventory.makeHeader.header inventory.makeHeader.header program distinct first.as_function_call start
      (bool_simple true) inputTypes inputMeanings (stages.descriptor_at inventory.makeHeader)
      (RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
  exact ⟨entry, type.trans inventory.makeHeader.make_result_type, handle, state, trace⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicInitialForward
/-! Initial Source success determines sufficient execution and export budgets
at the original public checkpoint. Every sufficient output appends its actual
new closure handle and retains all installed method cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = closureType .word ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType .word ∧
          ∃ returned : RetainedState inventory receiver completion.session [entry], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.makeInput, inventory.useInput, inventory.keepInput].map
      (fun input => input.prepared.index)).Nodup)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory inventory.makeHeader.header invocation ⟨[]⟩ [.bool true] (.value source) after) :
    InitialForwardAt inventory receiver first source after := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.makeHeader.header.function.context [.bool true] inventory.makeHeader.header.types := by
    rw [inventory.makeHeader.make_types]
    exact .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool true] [.bool true] :=
    .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have result : SourceCoreRawMetadata.runtimeType inventory.makeHeader.header.function.resultType =
      .function .unit .word := by
    rw [inventory.makeHeader.make_result_type]
    rfl
  have enough := RecursiveNamedPublicPhysicalSessionInitialForward.first_function
    inventory.rows fixture.recipePrepared inventory.makeHeader.header inventory.makeHeader.header
    program distinct first.as_function_call.toCall.toStartedCall start (bool_simple true)
    inputTypes inputMeanings result trace
  obtain ⟨requiredExecution, requiredOutput, enough⟩ := enough
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, succeeded, ready, entry, entryType, sourceEq, returned, handleType, state, heap⟩ :=
    enough executionFuel outputFuel outcome executionBound outputBound resumed
  exact ⟨completion, succeeded, ready, entry, entryType.trans inventory.makeHeader.make_result_type,
    sourceEq, returned, handleType.trans inventory.makeHeader.make_result_type, state, heap⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicStep
/-! Actual named calls with Word or Bool results continue the same retained session and Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.finished_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState inventory receiver call.completion.session entries,
      SourceCall inventory request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  exact RecursiveNamedPublicPhysicalSessionScalarStep.State.finished_call program fixture.recipePrepared state scalar call returned request inputs registry rawType nativeType descriptor invocation

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicFactoryForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

abbrev FactoryForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (resultType : TypeSystem.Ty) (source : Dynamic.Value)
    (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := entries)
    inventory.rows inventory.makeHeader.header receiver.completion observed.profile fixture.recipe call.toCall.toStartedCall .unit resultType source after

theorem forward_factory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    {resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = closureType resultType)
    (ready : session.ExportsReady)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value source) after) :
    FactoryForwardAt (entries := entries) inventory receiver call resultType source after := by
  exact RecursiveNamedPublicPhysicalSessionFunctionForward.forward_function program fixture.recipePrepared state call.toCall.toStartedCall request inputs
    (request.started.simple_registry state.registry simple) rawType ready trace

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

abbrev ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments)
    (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := entries)
    inventory.rows inventory.makeHeader.header receiver.completion observed.profile fixture.recipe scalar call.toStartedCall after

theorem forward_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) inventory receiver scalar call after := by
  exact RecursiveNamedPublicPhysicalSessionScalarForward.forward_call program fixture.recipePrepared state scalar call.toStartedCall request inputs registry rawType nativeType ready trace

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicSupports
/-! The single actual program certificate supplies named, closure and method
support together. The fixture retains only its original public header order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([makeInput, useInput, keepInput].map (fun input => input.prepared.index)).Nodup
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨program⟩ := admission.certificate.issue_for_checked fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    given.rows (admission.aligned given) (by rw [fixture.sameProgram]; exact fixture.checked)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by rw [given.indices]; exact observed.ordinarySlotsDistinct
    program := program }⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicFamily
/-! Public session proofs consume the static package generated by the actual
whole-program certificate. Body laws remain internal to production support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem StaticSupportPackage.program_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) (support : StaticSupportPackage fixture observed receiver.completion) :
    Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers support.toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      receiver.completion) := ⟨support.program⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value : Bool)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.bool value])
    (stages : ObservedStages fixture observed.makeRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.makeHeader.header call .word [.bool value] invocation) := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at
    fixture.recipePrepared [support.makeInput, support.useInput, support.keepInput]
    support.toOrdinaryInventory.rows state.atRecipe
    state.history.semantic.current.1 state.atSession (fun root found =>
      ⟨support.makeHeader.header, support.toOrdinaryInventory.selected_row observed.makeRow.toObservedRow
        support.makeHeader support.toOrdinaryInventory.make_member support.makeSlot root found⟩) call.started
  have selected : request.header = support.makeHeader.header :=
    selected_make_at support.makeHeader support.useHeader support.keepHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value] [.bool value] := by
    rw [selected, support.makeHeader.make_input_types]
    exact bool_inputs value
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.makeHeader.make_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.makeHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value) descriptor program invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by simpa only [selected] using trace⟩⟩

theorem RetainedState.use_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at
    fixture.recipePrepared [support.makeInput, support.useInput, support.keepInput]
    support.toOrdinaryInventory.rows state.atRecipe
    state.history.semantic.current.1 state.atSession (fun root found =>
      ⟨support.useHeader.header, support.toOrdinaryInventory.selected_row observed.useRow.toObservedRow
        support.useHeader support.toOrdinaryInventory.use_member support.useSlot root found⟩) call.started
  have selected : request.header = support.useHeader.header :=
    selected_use_at support.makeHeader support.useHeader support.keepHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useHeader.use_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useHeader.use_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useHeader.use_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    program invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by simpa only [selected] using trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.makeHeader.header sequence.second .word [.bool false]
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 41)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.makeHeader.header sequence.third .word [.bool false]
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 7)) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 41)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 7)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages useStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed admission receiver
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    program makeStages sequence.first
  obtain ⟨second⟩ := RetainedState.factory_meaning support initial false sequence.second makeStages
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.use_meaning support second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 41) sequence.firstRead sequence.firstValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨third⟩ := RetainedState.factory_meaning support firstRead.after
    false sequence.third makeStages
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.use_meaning support third.after second.entry
    (by simp) second.entryType second.handleEq (Core.Word.ofNatModulo 7) sequence.secondRead sequence.secondValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.use_meaning support secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 41) sequence.repeatedRead sequence.repeatedValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.use_meaning support repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 7) sequence.thirdRead sequence.thirdValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness makeStages useStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning makeStages useStages admission sequence receiver⟩

end Tests.SourceCoreCoercionPublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    program
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    program
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .word
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 41)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 7)) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 41)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 7)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver)
    : ForwardMeaning meaning := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver meaning.support
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      program
      meaning.firstTrace,
    meaning.secondMeaning.forward (bool_simple false) firstReady,
    meaning.firstReadMeaning.forward secondReady,
    meaning.thirdMeaning.forward (bool_simple false) firstReadReady,
    meaning.secondReadMeaning.forward thirdReady,
    meaning.repeatedReadMeaning.forward secondReadReady,
    meaning.thirdReadMeaning.forward repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness makeStages useStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed makeStages useStages
    admission sequence
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow.toObservedRow
  let useStages ← observeStages fixture observed.useRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning := closed_sequence_forward_meaning fixture observed makeStages useStages
    admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [5,11,17,29,35,47,59,71] do
    throw (IO.userError s!"coercion public stores changed: {reprStr stores}")
  IO.println "COERCION_PUBLIC_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar41/7/41/7; original constrained direct call and Bool-to-Word coercion"

end Tests.SourceCoreCoercionPublic
end
