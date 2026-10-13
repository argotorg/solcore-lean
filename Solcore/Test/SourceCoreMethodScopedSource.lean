import Solcore.Test.SourceCoreMethodClosureSource
import Solcore.Test.SourceCoreEvidenceScopedSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
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

abbrev Required := Tests.SourceCoreEvidenceScoped.Required
abbrev observeRequired := Tests.SourceCoreEvidenceScoped.observeRequired
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) (firstArgument secondArgument flagArgument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function (.product type (.product type .bool)) (closureType type))
  value : CallNode source (closureType type)
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)],
    .function (.product (.parameter parameter) (.product (.parameter parameter) .bool)) (closureType (.parameter parameter))⟩
  inputs : signature.parameterTypes = [.parameter parameter, .parameter parameter, .bool]
  returns : signature.returnTypes = [closureType (.parameter parameter)]
  exact : instantiation = ⟨signature.id, [(parameter, type)],
    .function (.product type (.product type .bool)) (closureType type), [predicate trait type], signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source signature parameter type firstArgument secondArgument flagArgument trait}
    (call : DirectCall source signature parameter type firstArgument secondArgument flagArgument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context type)
    (firstTyped : ExpressionHasType source context firstArgument type)
    (secondTyped : ExpressionHasType source context secondArgument type)
    (flagTyped : ExpressionHasType source context flagArgument .bool)
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
  have application : DeclarationApplicationValid context call.instantiation [type, type, .bool] (closureType type) [predicate trait type] := by
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
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.cons flagTyped (.nil _)))))
      call.value.raw resultFormed (call.value.type.symm ▸ resultFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty)
    (firstArgument secondArgument flagArgument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (DirectCall source signature parameter type firstArgument secondArgument flagArgument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product type (.product type .bool)) (closureType type))
  let value ← observeCallNode source value (closureType type)
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)) "generic direct form"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)], .function (.product (.parameter parameter) (.product (.parameter parameter) .bool)) (closureType (.parameter parameter))⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter parameter, .parameter parameter, .bool]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType (.parameter parameter)]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(parameter, type)], .function (.product type (.product type .bool)) (closureType type), [predicate trait type], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}


structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  firstRead : Read function.typedBody first type
  secondRead : Read function.typedBody second type
  flagRead : Read function.typedBody flag .bool
  call : DirectCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id trait
  statement : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = predicate trait type
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono type
  secondScheme : second.scheme = .mono type
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = closureType type
  inputTypes : signature.parameterTypes = [type, type, .bool]
  returns : signature.returnTypes = [closureType type]

def RootShape.nodeList {function signature generic parameter type trait}
    (shape : RootShape function signature generic parameter type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.flagRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic parameter type trait}
    (shape : RootShape function signature generic parameter type trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := closureType type, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest with
      | cons flagScheme flagExtended rest =>
        cases rest
        have fields : lexical.signatures = signatures := by
          rw [flagExtended.context_fields.1, secondExtended.context_fields.1, firstExtended.context_fields.1]
          rfl
        have types := StructuralSubstitution.TypesWellFormed.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.1.trans (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1))
          (flagExtended.context_fields.2.1.trans (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1))
          header.parameter_types
        have firstFormed := TypeAdmissible.ofWellFormed (types type (by simp [shape.inputTypes]))
        have currentLedger := ledger.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.2.1.trans (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1))
          (flagExtended.context_fields.2.2.2.2.trans (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2))
        have rowMember : shape.solved ∈ lexical.solvedRequirements := by
          rw [flagExtended.context_fields.2.2.2.2, secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
          exact shape.solvedMember
        have required : RequirementProves lexical shape.call.requirement (predicate trait type) :=
          ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
            currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
        have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_self))
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_scheme_requirements_self))
        have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements firstFormed
          (by cases flagExtended; exact .tail shape.flagSecond secondExtended.local_self)
          (by cases flagExtended; exact .tail shape.flagSecond secondExtended.local_scheme_requirements_self)
        have flagTyped := shape.flagRead.typed flagScheme shape.flagRequirements
          ⟨firstFormed.1, .builtin .bool⟩ flagExtended.local_self flagExtended.local_scheme_requirements_self
        have callTyped := shape.call.typed (fields ▸ member) firstFormed firstTyped secondTyped flagTyped required
        exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
          shape.statementForm callTyped shape.statementType)⟩
def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RootShape function signature generic parameter type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression readFlag, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst type
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond type
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag readFlag .bool
  let call ← observeDirect function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "flagSecond"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait type) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono type) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono type) "generic root secondScheme"
    let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flagScheme"
    let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "flagRequirements"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = closureType type) "generic root statementType"
    let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type, type, .bool]) "root inputTypes"
    let ⟨returns⟩ ← observed (signature.returnTypes = [closureType type]) "root returns"
    return {inputTypes, returns, flag, flagRead, flagFirst, flagSecond, flagScheme, flagRequirements, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")


structure MethodUnary (source : TypedSource) (type : TypeSystem.Ty) (argument : ExpressionId) where
  value : CallNode source type
  requirement : RequirementId
  form : value.node.form = .unary .bitNot argument
  requirements : value.node.requirements = [requirement]

theorem MethodUnary.typed {source type argument trait context}
    (call : MethodUnary source type argument) (catalog : TraitShape trait)
    (member : trait ∈ context.signatures.traits) (formed : TypeAdmissible context type)
    (argumentTyped : ExpressionHasType source context argument type)
    (required : RequirementProves context call.requirement (predicate (.declaration trait.id) type)) :
    ExpressionHasType source context call.value.node.id type := by
  have profile : UnaryOperatorHasType context .bitNot type type [call.requirement] :=
    .trait .bitNot (catalog.profile member type) (.cons required .nil)
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.unary argumentTyped profile)
      call.value.raw formed (call.value.type.symm ▸ formed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .ordinary profile.requirements_valid (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

def observeUnary (source : TypedSource) (type : TypeSystem.Ty)
    (argument : ExpressionId) (node : ExpressionNode) : IO (MethodUnary source type argument) := do
  let value ← observeCallNode source node type
  let [requirement] := node.requirements | throw (IO.userError "method requirement count")
  let ⟨form⟩ ← observed (value.node.form = .unary .bitNot argument) "method form"
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "method requirements"
  return {value, requirement, form, requirements}

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  localBinder : TypedBinder
  firstRead : Read function.typedBody first type
  call : MethodUnary function.typedBody type firstRead.node.id
  initialized : StatementNode
  conditionRead : Read function.typedBody flag .bool
  loopSecondRead : Read function.typedBody second type
  loopCall : MethodUnary function.typedBody type loopSecondRead.node.id
  assignment : StatementNode
  resolution : AssignmentResolution
  stop : TypedNode function.typedBody .bool
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
  finalRead : Read function.typedBody localBinder type
  finalCall : MethodUnary function.typedBody type finalRead.node.id
  statement : StatementNode
  callRequired : Required function call.requirement (predicate trait type)
  loopRequired : Required function loopCall.requirement (predicate trait type)
  finalRequired : Required function finalCall.requirement (predicate trait type)
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono type
  secondScheme : second.scheme = .mono type
  flagScheme : flag.scheme = .mono .bool
  localScheme : localBinder.scheme = .mono type
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  flagRequirements : flag.schemeRequirements = []
  localRequirements : localBinder.schemeRequirements = []
  firstClosed : type.freeVariables = []
  flagOwner : flag.id.owner = function.typedBody.owner
  localOwner : localBinder.id.owner = function.typedBody.owner
  localOrdinary : localBinder.comptime = false
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  localFirst : localBinder.id ≠ first.id
  localSecond : localBinder.id ≠ second.id
  localFlag : localBinder.id ≠ flag.id
  expression : TypedNode function.typedBody (closureType type)
  outerReturn : StatementNode
  inputTypes : signature.parameterTypes = [type, type, .bool]
  returns : signature.returnTypes = [closureType type]
  roots : function.typedBody.roots = [.statement outerReturn.id]
  lambda : expression.node.form = .lambda [] type [initialized.id, loop.id, statement.id]
  outerReturnFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some expression.node.id)
  outerReturnType : outerReturn.type = closureType type
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some call.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = first.id
  targetType : resolution.target.type = type
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  stopForm : stop.node.form = .reference "false" (.builtinBoolean false)
  flagAssignmentFound : function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment
  flagAssignmentForm : flagAssignment.form = .assignValue flagResolution .equal stop.node.id
  flagAssignmentType : flagAssignment.type = .unit
  flagTargetRoot : flagResolution.target.root = flag.id
  flagTargetType : flagResolution.target.type = .bool
  flagTargetBare : flagResolution.target.projections = []
  flagAssignmentRequirements : flagResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalCall.value.node.id)
  statementType : statement.type = type

def FactoryShape.body {function signature type trait}
    (shape : FactoryShape function signature type trait) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def FactoryShape.nodeList {function signature type trait}
    (shape : FactoryShape function signature type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.conditionRead.node, .expression shape.loopSecondRead.node,
   .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.value.node, .statement shape.statement,
   .expression shape.expression.node, .statement shape.outerReturn]


theorem FactoryShape.statementTyping {function signature type trait}
    (shape : FactoryShape function signature type (.declaration trait.id))
    (catalog : TraitShape trait) (signatures : ProgramSignatures) (member : trait ∈ signatures.traits)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.outerReturn.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
  let facts : StatementFacts := ⟨type, true, true, .returned⟩
  refine ⟨BodyFacts.singleton ⟨closureType type, true, true, .returned⟩, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest with
      | cons flagScheme flagExtended rest =>
        cases rest
        have fields : lexical.signatures = signatures := by
          rw [flagExtended.context_fields.1, secondExtended.context_fields.1, firstExtended.context_fields.1]
          rfl
        have types := StructuralSubstitution.TypesWellFormed.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.1.trans (secondExtended.context_fields.2.2.1.trans firstExtended.context_fields.2.2.1))
          (flagExtended.context_fields.2.1.trans (secondExtended.context_fields.2.1.trans firstExtended.context_fields.2.1))
          header.parameter_types
        have firstFormed := TypeAdmissible.ofWellFormed (types type (by simp [shape.inputTypes]))
        have currentLedger := ledger.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.2.1.trans (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1))
          (flagExtended.context_fields.2.2.2.2.trans (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2))
        have rows : lexical.solvedRequirements = function.solvedRequirements := by
          rw [flagExtended.context_fields.2.2.2.2, secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
          rfl
        have firstLookup : lexical.LocalLookup shape.first.id shape.first.scheme := by
          cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_self)
        have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_self))
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_scheme_requirements_self))
        have secondLookup : lexical.LocalLookup shape.second.id shape.second.scheme := by
          cases flagExtended; exact .tail shape.flagSecond secondExtended.local_self
        have secondRequirements : lexical.LocalSchemeRequirementsLookup shape.second.id shape.second.schemeRequirements := by
          cases flagExtended; exact .tail shape.flagSecond secondExtended.local_scheme_requirements_self
        have callTyped := shape.call.typed catalog (fields ▸ member) firstFormed firstTyped
          (shape.callRequired.proves currentLedger rows shape.noTemplates)
        let inner := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
        have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder inner := by
          apply BinderExtends.intro
          · exact { owned := shape.localOwner
                    scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible firstFormed
                    quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                    monomorphic_requirements_empty := fun _ => shape.localRequirements }
          · cases flagExtended; cases secondExtended; cases firstExtended
            simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext, Context.ofSignatures,
              Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements,
              Context.withResidualTypeVariables, shape.localFirst, shape.localSecond, shape.localFlag]
        have innerFirst : TypeAdmissible inner type := StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := inner) rfl rfl rfl rfl rfl firstFormed
        have innerSecond : TypeAdmissible inner type := StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := inner) rfl rfl rfl rfl rfl firstFormed
        have innerBool : TypeAdmissible inner .bool := ⟨innerFirst.1, .builtin .bool⟩
        have innerLedger : ScopedRequirementLedgerWellFormed inner function.typedBody := ScopedRequirementLedgerWellFormed.transportContext (source := lexical) (target := inner) rfl rfl rfl currentLedger
        have conditionTyped := shape.conditionRead.typed flagScheme shape.flagRequirements innerBool
          (.tail shape.localFlag flagExtended.local_self) (.tail shape.localFlag flagExtended.local_scheme_requirements_self)
        have loopSecondTyped := shape.loopSecondRead.typed secondScheme shape.secondRequirements innerSecond
          (.tail shape.localSecond secondLookup) (.tail shape.localSecond secondRequirements)
        have loopCallTyped := shape.loopCall.typed catalog (fields ▸ member) innerFirst loopSecondTyped
          (shape.loopRequired.proves innerLedger rows shape.noTemplates)
        have finalTyped := shape.finalRead.typed shape.localScheme shape.localRequirements innerFirst
          localExtended.local_self localExtended.local_scheme_requirements_self
        have finalCallTyped := shape.finalCall.typed catalog (fields ▸ member) innerFirst finalTyped
          (shape.finalRequired.proves innerLedger rows shape.noTemplates)
        have stopTyped := shape.stop.ordinary innerBool (shape.stopForm ▸ .reference (.builtinBoolean false))
        have writable : WritableLocal inner shape.resolution.target.root type := by
          rw [shape.targetRoot]
          exact .intro (.tail shape.localFirst firstLookup) (shape.firstScheme.symm ▸ SchemeWellFormed.monoAdmissible innerFirst)
            (by rw [shape.firstScheme]; rfl) (by rw [shape.firstScheme]; rfl)
        have assigned : StatementHasType function.typedBody ⟨type, 1⟩ inner shape.assignment.id inner ordinary :=
          .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
            (.equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
              loopCallTyped shape.assignmentRequirements) shape.assignmentType
        have flagWritable : WritableLocal inner shape.flagResolution.target.root .bool := by
          rw [shape.flagTargetRoot]
          exact .intro (.tail shape.localFlag flagExtended.local_self) (flagScheme.symm ▸ SchemeWellFormed.monoAdmissible innerBool)
            (by rw [flagScheme]; rfl) (by rw [flagScheme]; rfl)
        have flagAssigned : StatementHasType function.typedBody ⟨type, 1⟩ inner shape.flagAssignment.id inner ordinary :=
          .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm
            (.equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType)
              stopTyped shape.flagAssignmentRequirements) shape.flagAssignmentType
        have loopTyped := StatementHasType.whileLoop (control := ⟨type, 0⟩)
          (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
          (.cons assigned (.singleton flagAssigned)) shape.loopType
        have initializedTyped : StatementHasType function.typedBody ⟨type, 0⟩ lexical shape.initialized.id inner ordinary := by
          apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
          · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using callTyped
          · rw [shape.localScheme]; rfl
          · simp [shape.localScheme, SchemeGeneralizes, SchemeGeneralizesExcept, TypeSystem.Scheme.mono, shape.firstClosed]
          · exact localExtended
          · exact shape.initializedType
        have bodyTyped : StatementsHaveType function.typedBody ⟨type, 0⟩ lexical
            [shape.initialized.id, shape.loop.id, shape.statement.id] inner
            (BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts))) :=
          .cons initializedTyped (.cons loopTyped (.singleton (.returnValue
            (lookupStatement?_sound shape.statementFound) shape.statementForm finalCallTyped shape.statementType)))
        have callable : TypeAdmissible lexical (closureType type) :=
          ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin
            (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
        have lambdaTyped := shape.expression.ordinary callable
          (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _) bodyTyped
            (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩))
        exact ⟨lexical, .singleton (.returnValue (lookupStatement?_sound shape.outerReturnFound)
          shape.outerReturnForm lambdaTyped shape.outerReturnType)⟩


def observeFactory (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (FactoryShape function signature type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression firstNode, .expression initialValue, .statement initialized,
      .expression conditionNode, .expression loopSecondNode, .expression loopValue, .statement assignment,
      .expression stopNode, .statement flagAssignment, .statement loop,
      .expression finalNode, .expression finalValue, .statement statement,
      .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
      | throw (IO.userError "factory fifteen nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "relay initialized binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "relay saved assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "relay flag assignment")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first firstNode type
  let call ← observeUnary function.typedBody type firstRead.node.id initialValue
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let loopSecondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second loopSecondNode type
  let loopCall ← observeUnary function.typedBody type loopSecondRead.node.id loopValue
  let stop ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody stopNode .bool
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder finalNode type
  let finalCall ← observeUnary function.typedBody type finalRead.node.id finalValue
  let callRequired ← observeRequired function call.requirement (predicate trait type)
  let loopRequired ← observeRequired function loopCall.requirement (predicate trait type)
  let finalRequired ← observeRequired function finalCall.requirement (predicate trait type)
  let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "relay noTemplates"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "relay inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono type) "relay firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono type) "relay secondScheme"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "relay flagScheme"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono type) "relay localScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "relay firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "relay secondRequirements"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "relay flagRequirements"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "relay localRequirements"
  let ⟨firstClosed⟩ ← observed (type.freeVariables = []) "relay firstClosed"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "relay flagOwner"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "relay localOwner"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "relay localOrdinary"
  let ⟨different⟩ ← observed (second.id ≠ first.id) "relay different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "relay flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "relay flagSecond"
  let ⟨localFirst⟩ ← observed (localBinder.id ≠ first.id) "relay localFirst"
  let ⟨localSecond⟩ ← observed (localBinder.id ≠ second.id) "relay localSecond"
  let ⟨localFlag⟩ ← observed (localBinder.id ≠ flag.id) "relay localFlag"
  let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType type)
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type, type, .bool]) "factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType type]) "factory returns"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "factory roots"
  let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] type [initialized.id, loop.id, statement.id]) "factory lambda"
  let ⟨outerReturnFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "outerReturnFound"
  let ⟨outerReturnForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.node.id)) "outerReturnForm"
  let ⟨outerReturnType⟩ ← observed (outerReturn.type = closureType type) "outerReturnType"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "relay initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some call.value.node.id)) "relay initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "relay initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "relay assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "relay assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "relay assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = first.id) "relay targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = type) "relay targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "relay targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "relay assignmentRequirements"
  let ⟨stopForm⟩ ← observed (stop.node.form = .reference "false" (.builtinBoolean false)) "relay stopForm"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "relay flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stop.node.id) "relay flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "relay flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "relay flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "relay flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "relay flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "relay flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "relay loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "relay loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "relay loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalCall.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "relay statementType"
  return {expression, outerReturn, inputTypes, returns, lambda, outerReturnFound, outerReturnForm, outerReturnType, first, second, flag, localBinder, firstRead, call, initialized, conditionRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalCall, statement, callRequired, loopRequired, finalRequired, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
abbrev UseShape := Tests.SourceCoreMethodClosure.UseShape
abbrev observeUse := Tests.SourceCoreMethodClosure.observeUse

def content : String := String.intercalate "\n" [
  "trait BitNot<T> { function bnot(value: T) returns (T); }",
  "impl BitNot<Word> { function bnot(value: Word) returns (Word) { return value; } }",
  "impl BitNot<Bool> { function bnot(value: Bool) returns (Bool) { return value; } }",
  "function make<T>(value: T, next: T, flag: Bool) returns (function() returns (T)) where T: BitNot { return lam() -> T { let saved = ~value; while (flag) { value = ~next; flag = false; } return ~saved; }; }",
  "function wordRoot(value: Word, next: Word, flag: Bool) returns (function() returns (Word)) { return make(value, next, flag); }",
  "function boolRoot(value: Bool, next: Bool, flag: Bool) returns (function() returns (Bool)) { return make(value, next, flag); }",
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
  makeShape : FactoryShape makeFunction makeSignature (.parameter parameter) (.declaration trait.id)
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
      let makeShape ← observeFactory makeFunction makeSignature (.parameter parameter) (.declaration trait.id)
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

end Tests.SourceCoreMethodScoped
