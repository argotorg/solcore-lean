import Solcore.Test.SourceCoreEvidenceDirectSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
def mark (trait : ProgramTraitId) (type : TypeSystem.Ty) : ProgramPredicate := ⟨trait, type, []⟩
abbrev ChooseShape := Tests.SourceCoreEvidenceDirect.ChooseShape
abbrev observeChoose := Tests.SourceCoreEvidenceDirect.observeChoose
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode
abbrev closureType (type : TypeSystem.Ty) : TypeSystem.Ty := .function .unit type
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

structure FactoryCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId)
    (firstType secondType : TypeSystem.Ty) (firstArgument secondArgument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function (.product firstType secondType) (closureType firstType))
  value : CallNode source (closureType firstType)
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)
  different : firstParameter ≠ secondParameter
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (closureType (.parameter firstParameter))⟩
  inputs : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [closureType (.parameter firstParameter)]
  exact : instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)],
    .function (.product firstType secondType) (closureType firstType), [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩

theorem FactoryCall.typed {source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait}
    (call : FactoryCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context firstType) (secondFormed : TypeAdmissible context secondType)
    (firstTyped : ExpressionHasType source context firstArgument firstType)
    (secondTyped : ExpressionHasType source context secondArgument secondType)
    (required : RequirementProves context call.requirement (mark trait firstType)) :
    ExpressionHasType source context call.value.node.id (closureType firstType) := by
  have closureFormed : TypeAdmissible context (closureType firstType) := ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · refine ⟨by simp [call.scheme, call.different], ?_⟩
      simpa only [ParameterSubstitution.domain, List.map_cons, List.map_nil, call.scheme] using
        List.Perm.swap firstParameter secondParameter []
    · intro parameter replacement contained
      rcases List.mem_cons.mp contained with same | contained
      · cases same; exact secondFormed
      · cases List.mem_singleton.mp contained; exact firstFormed
    · simp [call.scheme, closureType, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.scheme, mark, ProgramPredicate.applyParameters, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
  have application : DeclarationApplicationValid context call.instantiation [firstType, secondType] (closureType firstType) [mark trait firstType] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, call.returns, closureType, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.nil _))))
      call.value.raw closureFormed (call.value.type.symm ▸ closureFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : FactoryCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id trait
  statement : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = mark trait firstType
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = closureType firstType

def RootShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType])
    (returns : signature.returnTypes = [closureType firstType]) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let facts : StatementFacts := {type := closureType firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have types := StructuralSubstitution.TypesWellFormed.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1)
        (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1)
        header.parameter_types
      have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
      have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
      have currentLedger := ledger.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1)
        (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2)
      have rowMember : shape.solved ∈ lexical.solvedRequirements := by
        rw [secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
        exact shape.solvedMember
      have required : RequirementProves lexical shape.call.requirement (mark trait firstType) :=
        ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
          currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped required
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm callTyped shape.statementType)⟩


def observeFactoryCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty)
    (firstArgument secondArgument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (FactoryCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product firstType secondType) (closureType firstType))
  let value ← observeCallNode source value (closureType firstType)
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)) "generic direct form"
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "generic direct different"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (closureType (.parameter firstParameter))⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType (.parameter firstParameter)]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)], .function (.product firstType secondType) (closureType firstType), [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, different, scheme, inputs, returns, exact}

def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RootShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← observeFactoryCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = mark trait firstType) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = closureType firstType) "generic root statementType"
    return {first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")

structure FactoryShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : Tests.SourceCoreEvidenceDirect.DirectCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id trait
  statement : StatementNode
  expression : ExpressionNode
  outerReturn : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = mark trait firstType
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement outerReturn.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = firstType

  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  lambda : expression.form = .lambda [] firstType [statement.id]
  expressionRaw : expression.rawType = closureType firstType
  expressionType : expression.type = closureType firstType
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  outerFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerForm : outerReturn.form = .returnStmt (some expression.id)
  outerType : outerReturn.type = closureType firstType

def FactoryShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement, .expression shape.expression, .statement shape.outerReturn]

theorem FactoryShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType])
    (returns : signature.returnTypes = [closureType firstType]) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.outerReturn.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let facts : StatementFacts := {type := closureType firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have types := StructuralSubstitution.TypesWellFormed.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1)
        (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1)
        header.parameter_types
      have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
      have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
      have currentLedger := ledger.transportContext
        (secondExtended.context_fields.1.trans firstExtended.context_fields.1)
        (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1)
        (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2)
      have rowMember : shape.solved ∈ lexical.solvedRequirements := by
        rw [secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
        exact shape.solvedMember
      have required : RequirementProves lexical shape.call.requirement (mark trait firstType) :=
        ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
          currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped required
      have callable : TypeAdmissible lexical (closureType firstType) :=
        ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
      have lambdaTyped : ExpressionHasType function.typedBody lexical shape.expression.id (closureType firstType) := by
        rw [← shape.expressionType]
        refine .intro (lookupExpression?_sound shape.expressionFound)
          (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
            (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
              shape.statementForm callTyped shape.statementType))
            (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
        rw [shape.requirements, shape.coercions, shape.expressionType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.outerFound)
        shape.outerForm lambdaTyped shape.outerType)⟩


def observeFactory (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement, .expression expression, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← Tests.SourceCoreEvidenceDirect.observeDirect function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = mark trait firstType) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = firstType) "generic root statementType"
    let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "factory expressionFound"
    let ⟨lambda⟩ ← observed (expression.form = .lambda [] firstType [statement.id]) "factory lambda"
    let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType firstType) "factory expressionRaw"
    let ⟨expressionType⟩ ← observed (expression.type = closureType firstType) "factory expressionType"
    let ⟨requirements⟩ ← observed (expression.requirements = []) "factory requirements"
    let ⟨coercions⟩ ← observed (expression.coercions = []) "factory coercions"
    let ⟨outerFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "factory outerFound"
    let ⟨outerForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.id)) "factory outerForm"
    let ⟨outerType⟩ ← observed (outerReturn.type = closureType firstType) "factory outerType"
    return {expression, outerReturn, expressionFound, lambda, expressionRaw, expressionType, requirements, coercions, outerFound, outerForm, outerType, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function choose<A, B>(a: A, b: B) returns (A) where A: Mark { return a; }",
    "function factory<A, B>(a: A, b: B) returns (function() returns (A)) where A: Mark { return lam() -> A { return choose(a, b); }; }",
    "function wordRoot(value: Word, flag: Bool) returns (function() returns (Word)) { return factory(value, flag); }",
    "function boolRoot(flag: Bool, value: Word) returns (function() returns (Bool)) { return factory(flag, value); }"]}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitId
  chooseFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  factoryFunction : CheckedFunction
  factorySignature : ProgramFunctionSignature
  wordFunction : CheckedFunction
  wordSignature : ProgramFunctionSignature
  boolFunction : CheckedFunction
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [chooseFunction, factoryFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [chooseSignature, factorySignature, wordSignature, boolSignature]
  methods : program.methods = []
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  factoryDeclaration : factoryFunction.declaration = factorySignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  chooseFactory : chooseSignature.id ≠ factorySignature.id
  chooseWord : chooseSignature.id ≠ wordSignature.id
  chooseBool : chooseSignature.id ≠ boolSignature.id
  factoryWord : factorySignature.id ≠ wordSignature.id
  factoryBool : factorySignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  chooseShape : ChooseShape chooseFunction chooseSignature trait
  factoryFirstParameter : TypeSystem.TypeParameterId
  factorySecondParameter : TypeSystem.TypeParameterId
  factoryScheme : factorySignature.scheme = ⟨[factoryFirstParameter, factorySecondParameter], [mark trait (.parameter factoryFirstParameter)], .function (.product (.parameter factoryFirstParameter) (.parameter factorySecondParameter)) (closureType (.parameter factoryFirstParameter))⟩
  factoryShape : FactoryShape factoryFunction factorySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter factoryFirstParameter) (.parameter factorySecondParameter) trait
  wordShape : RootShape wordFunction wordSignature factorySignature factoryFirstParameter factorySecondParameter .word .bool trait
  boolShape : RootShape boolFunction boolSignature factorySignature factoryFirstParameter factorySecondParameter .bool .word trait
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  factoryInputTypes : factorySignature.parameterTypes = [(.parameter factoryFirstParameter), (.parameter factorySecondParameter)]
  factoryReturns : factorySignature.returnTypes = [closureType (.parameter factoryFirstParameter)]
  factoryNodes : factoryFunction.typedBody.nodes = factoryShape.nodeList
  wordInputTypes : wordSignature.parameterTypes = [.word, .bool]
  wordReturns : wordSignature.returnTypes = [closureType .word]
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolInputTypes : boolSignature.parameterTypes = [.bool, .word]
  boolReturns : boolSignature.returnTypes = [closureType .bool]
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList

private theorem checkedHeader {program : CheckedProgram} (checked : checkProgram workspace 1000 = .ok program)
    {function signature} (member : function ∈ program.functions) (signatureMember : signature ∈ program.signatures.functions)
    (accepted : checkFunctionBody program.environment program.signatures signature 1000 = .ok function) :
    CheckedBodyHeaderWellFormed program.signatures signature function := by
  obtain ⟨other, otherMember, header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked member
  have same : other = signature := eq_of_mem_of_nodup_map
    (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids otherMember signatureMember
    (header.declaration_eq.symm.trans (checkFunctionBody_success_declaration accepted))
  exact same ▸ header

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [chooseFunction, factoryFunction, wordFunction, boolFunction], [chooseSignature, factorySignature, wordSignature, boolSignature] =>
      let [predicate] := chooseSignature.scheme.predicates | throw (IO.userError "choose predicate")
      let trait := predicate.trait
      let chooseShape ← observeChoose chooseFunction chooseSignature trait
      let [factoryFirstParameter, factorySecondParameter] := factorySignature.scheme.parameters | throw (IO.userError "factory parameters")
      let ⟨factoryScheme⟩ ← observed (factorySignature.scheme = ⟨[factoryFirstParameter, factorySecondParameter], [mark trait (.parameter factoryFirstParameter)], .function (.product (.parameter factoryFirstParameter) (.parameter factorySecondParameter)) (closureType (.parameter factoryFirstParameter))⟩) "factory scheme"
      let factoryShape ← observeFactory factoryFunction factorySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter factoryFirstParameter) (.parameter factorySecondParameter) trait
      let wordShape ← observeRoot wordFunction wordSignature factorySignature factoryFirstParameter factorySecondParameter .word .bool trait
      let boolShape ← observeRoot boolFunction boolSignature factorySignature factoryFirstParameter factorySecondParameter .bool .word trait
      let ⟨methods⟩ ← observed (program.methods = []) "fixture methods"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "choose declaration"
      let ⟨factoryDeclaration⟩ ← observed (factoryFunction.declaration = factorySignature.id) "factory declaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
      let ⟨chooseFactory⟩ ← observed (chooseSignature.id ≠ factorySignature.id) "chooseFactory distinct"
      let ⟨chooseWord⟩ ← observed (chooseSignature.id ≠ wordSignature.id) "chooseWord distinct"
      let ⟨chooseBool⟩ ← observed (chooseSignature.id ≠ boolSignature.id) "chooseBool distinct"
      let ⟨factoryWord⟩ ← observed (factorySignature.id ≠ wordSignature.id) "factoryWord distinct"
      let ⟨factoryBool⟩ ← observed (factorySignature.id ≠ boolSignature.id) "factoryBool distinct"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "wordBool distinct"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "choose nodes"
      let ⟨factoryInputTypes⟩ ← observed (factorySignature.parameterTypes = [(.parameter factoryFirstParameter), (.parameter factorySecondParameter)]) "factory original input types"
      let ⟨factoryReturns⟩ ← observed (factorySignature.returnTypes = [closureType (.parameter factoryFirstParameter)]) "factory original returns"
      let ⟨factoryNodes⟩ ← observed (factoryFunction.typedBody.nodes = factoryShape.nodeList) "factory nodes"
      let ⟨wordInputTypes⟩ ← observed (wordSignature.parameterTypes = [.word, .bool]) "word original input types"
      let ⟨wordReturns⟩ ← observed (wordSignature.returnTypes = [closureType .word]) "word original returns"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "word nodes"
      let ⟨boolInputTypes⟩ ← observed (boolSignature.parameterTypes = [.bool, .word]) "bool original input types"
      let ⟨boolReturns⟩ ← observed (boolSignature.returnTypes = [closureType .bool]) "bool original returns"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "bool nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          have header := checkedHeader checked member candidateMember accepted
          have ledger := SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
            (checkProgram_success_signature_formation checked) candidateMember accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl | rfl
          · exact chooseShape.statementTyping program.signatures
          · exact False.elim (chooseFactory (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseFactory (identity.symm.trans factoryDeclaration))
          · exact factoryShape.statementTyping program.signatures (by simp [signatures]) header ledger factoryInputTypes factoryReturns
          · exact False.elim (factoryWord (factoryDeclaration.symm.trans identity))
          · exact False.elim (factoryBool (factoryDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (identity.symm.trans wordDeclaration))
          · exact False.elim (factoryWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) header ledger wordInputTypes wordReturns
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (identity.symm.trans boolDeclaration))
          · exact False.elim (factoryBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) header ledger boolInputTypes boolReturns
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep, program, checked, trait, chooseFunction, factoryFunction, wordFunction, boolFunction, chooseSignature, factorySignature, wordSignature, boolSignature, functions, signatures, methods, chooseDeclaration, factoryDeclaration, wordDeclaration, boolDeclaration, chooseFactory, chooseWord, chooseBool, factoryWord, factoryBool, wordBool, chooseShape, factoryFirstParameter, factorySecondParameter, factoryScheme, factoryShape, wordShape, boolShape, chooseNodes, factoryInputTypes, factoryReturns, factoryNodes, wordInputTypes, wordReturns, wordNodes, boolInputTypes, boolReturns, boolNodes}
    | _, _ => throw (IO.userError "evidence direct declarations")
end Tests.SourceCoreEvidenceClosure
