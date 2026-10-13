import Solcore.Test.SourceCoreMethodOriginEvidenceSource
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
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
